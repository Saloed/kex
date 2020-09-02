package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.ConcreteClass
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.ir.OuterClass

internal fun Class.property(propertyName: String): Pair<Set<Field>, KexType> {
    val field = findField(propertyName)
    if (field != null) {
        return setOf(field) to field.type.kexType
    }
    val fields = allInheritors().mapNotNull { it.findField(propertyName) }.toSet()
    if (fields.isEmpty()) error("Class $this and it inheritors has no field $propertyName")
    val fieldType = fields.map { it.type.kexType }.groupBy({ it }, { 1 }).maxByOrNull { (_, cnt) -> cnt.sum() }?.key ?: error("No types")
    return fields to fieldType
}

internal fun Class.allInheritors() = cm.concreteClasses.filter { it.isInheritorOf(this) }.toSet()

private fun Class.findFieldConcrete(name: String): Field? {
    return fields.find { it.name == name } ?: superClass?.findFieldConcrete(name)
}

private fun Class.findField(name: String): Field? {
    val myField = fields.find { it.name == name }
    if (myField != null) return myField
    var parents = (listOf(superClass) + interfaces).filterNotNull()

    var result = parents.mapNotNull { it as? ConcreteClass }.mapNotNull { it.findFieldConcrete(name) }.firstOrNull()
    while (parents.isNotEmpty()) {
        if (result != null) break
        parents = parents
                .map { (listOf(it.superClass) + it.interfaces).filterNotNull() }
                .flatten()
        result = parents.mapNotNull { it as? ConcreteClass }.mapNotNull { it.findFieldConcrete(name) }.firstOrNull()
    }

    return result
            ?: (listOf(superClass) + interfaces).filterNotNull().mapNotNull { it as? OuterClass }.map { it.findFieldConcrete(name) }.firstOrNull()
}
