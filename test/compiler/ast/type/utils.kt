package compiler.ast.type

import compiler.binding.type.BaseType

fun fakeType(name: String, vararg superTypes: BaseType): BaseType = object: BaseType {
    override fun toString() = name
    override val superTypes = superTypes.toSet()
    override val simpleName = name
    override val fullyQualifiedName = name
}