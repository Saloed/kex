package org.jetbrains.research.kex.generator

import com.abdullin.kthelper.`try`
import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.annotations.AnnotationManager
import org.jetbrains.research.kex.asm.analysis.KexCheckerException
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.random.GenerationException
import org.jetbrains.research.kex.smt.Checker
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.smt.SMTModel
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method

private val visibilityLevel by lazy { kexConfig.getEnumValue("apiGeneration", "visibility", true, Visibility.PUBLIC) }
private val apiGeneration get() = kexConfig.getBooleanValue("apiGeneration", "enabled", false)
private val useConcreteImpl get() = kexConfig.getBooleanValue("apiGeneration", "use-concrete-impl", false)

class NoConcreteInstanceException(val klass: Class) : Exception()

class Generator(val ctx: ExecutionContext, val psa: PredicateStateAnalysis) {
    val cm: ClassManager get() = ctx.cm
    val csGenerator = CallStackGenerator(ctx, psa)
    val csExecutor = CallStackExecutor(ctx)

    private fun generateAPI(method: Method, state: PredicateState, model: SMTModel) = try {
        val descriptors = generateFinalDescriptors(method, ctx, model, state).concrete
        log.debug("Generated descriptors:")
        log.debug(descriptors)
        val thisCallStack = descriptors.first?.let { descriptor ->
            csGenerator.generate(descriptor)
        }
        val argCallStacks = descriptors.second.map { descriptor ->
            csGenerator.generate(descriptor)
        }
        thisCallStack?.let { csExecutor.execute(it) } to argCallStacks.map { csExecutor.execute(it) }.toTypedArray()
    } catch (e: Exception) {
        throw GenerationException(e)
    }

    fun generateFromModel(method: Method, state: PredicateState, model: SMTModel) =
            generateInputByModel(ctx, method, state, model)

    private val Class.isInstantiable: Boolean
        get() = when {
            this.isAbstract -> false
            this.isInterface -> false
            !this.isStatic && this.outerClass != null -> false
            else -> true
        }

    private val Descriptor.concrete
        get() = when (this) {
            is ObjectDescriptor -> this.instantiableDescriptor
            else -> this
        }

    private val ObjectDescriptor.instantiableDescriptor: ObjectDescriptor
        get() {
            val concreteClass = when {
                this.klass.isInstantiable -> this.klass
                else -> `try` {
                    cm.concreteClasses.filter {
                        klass.isAncestorOf(it) && it.isInstantiable && visibilityLevel <= it.visibility
                    }.random()
                }.getOrElse {
                    throw NoConcreteInstanceException(this.klass)
                }
            }
            val result = ObjectDescriptor(klass = concreteClass)
            for ((name, desc) in this.fields) {
                result[name] = desc.copy(owner = result, value = desc.value.concrete)
            }
            return result
        }

    private val Pair<Descriptor?, List<Descriptor>>.concrete
        get() =
            first?.concrete to second.map { it.concrete }

    private val Pair<Descriptor?, List<Descriptor>>.typeInfoState: PredicateState
        get() {
            val thisState = first?.run {
                val typeInfo = generateTypeInfo()
                TermRemapper(mapOf(term to term { `this`(term.type) })).apply(typeInfo)
            }
            val argStates = second.mapIndexed { index, descriptor ->
                val typeInfo = descriptor.generateTypeInfo()
                TermRemapper(mapOf(descriptor.term to term { arg(descriptor.term.type, index) })).apply(typeInfo)
            }.toTypedArray()
            return listOfNotNull(thisState, *argStates).fold(emptyState()) { acc, predicateState -> acc + predicateState }
        }

    private fun prepareState(method: Method, ps: PredicateState, typeInfoMap: TypeInfoMap) = transform(ps) {
        +AnnotationIncluder(AnnotationManager.defaultLoader)
        +ConcreteImplInliner(ctx, typeInfoMap, psa)
        +IntrinsicAdapter
        +ReflectionInfoAdapter(method, ctx.loader)
        +Optimizer()
        +ConstantPropagator
        +BoolTypeAdapter(method.cm.type)
        +ArrayBoundsAdapter()
        +NullityInfoAdapter()
        +CastInfoAdapter(method.cm.type)
    }

    private fun reExecute(method: Method, block: BasicBlock, typeInfoState: PredicateState): Pair<Any?, Array<Any?>> {
        val checker = Checker(method, ctx.loader, psa)
        val ps = typeInfoState.let {
            val ps = checker.createState(block.terminator)!!
            val (t, a) = collectArguments(it)
            val (at, aa) = collectArguments(ps)
            val map = mutableMapOf<Term, Term>()
            at?.run { map[at] == t }
            aa.forEach { (key, value) -> a[key]?.let { map[value] = it } }
            TermRemapper(map).apply(ps)
        }
        val typeInfoMap = collectPlainTypeInfos(ctx.types, typeInfoState)
        val preparedState = prepareState(method, ps, typeInfoMap)

        val result = try {
            checker.check(preparedState, preparedState.path)
        } catch (e: Exception) {
            throw KexCheckerException(e, ps)
        }
        return when (result) {
            is Result.SatResult -> generateAPI(method, checker.state, result.model)
            else -> throw GenerationException("ReExecuted state can't be solved: $result")
        }
    }

    fun generateConcreteAPI(method: Method, block: BasicBlock, state: PredicateState, model: SMTModel) = try {
        val descriptors = generateFinalDescriptors(method, ctx, model, state).concrete
        log.debug("Generated descriptors:")
        log.debug(descriptors)
        val typeInfoState = descriptors.typeInfoState
        reExecute(method, block, typeInfoState)
    } catch (e: Exception) {
        throw GenerationException(e)
    }

    fun generate(method: Method, block: BasicBlock, state: PredicateState, model: SMTModel) = when {
        apiGeneration -> when {
            useConcreteImpl -> generateAPI(method, state, model)
            else -> generateConcreteAPI(method, block, state, model)
        }
        else -> generateFromModel(method, state, model)
    }
}