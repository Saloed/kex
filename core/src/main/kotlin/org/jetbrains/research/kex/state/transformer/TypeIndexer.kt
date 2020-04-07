package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.term.InstanceOfTerm
import org.jetbrains.research.kex.state.term.Term

object TypeIndex {
    private var typeIdx = 1
    private val index = hashMapOf<KexType, Int>()
    fun getOrCreate(type: KexType) = index.getOrPut(type) { 10 * typeIdx++ }
    fun read(type: KexType) = index[type]
    fun findType(idx: Int) = index.entries.find { (_, id) -> id == idx }?.key
            ?: unreachable { log.error("No type for index: $idx") }
}

val Term.typeIdx: Int
    get() = TypeIndex.read(type)
            ?: unreachable { log.error("No index for type: $type") }

val KexType.typeIdx: Int
    get() = TypeIndex.read(this)
            ?: unreachable { log.error("No index for type: $this") }

object TypeIndexer : Transformer<TypeIndexer> {
    override fun transformTerm(term: Term): Term {
        super.transformTerm(term)
        TypeIndex.getOrCreate(term.type)
        return term
    }

    override fun transformInstanceOfTerm(term: InstanceOfTerm): Term {
        super.transformInstanceOfTerm(term)
        TypeIndex.getOrCreate(term.checkedType)
        return term
    }
}
