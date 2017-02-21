package compiler.ast.type

val Integer = object : BaseType {
    override val impliedModifier = TypeModifier.IMMUTABLE
    override val simpleName = "Integer"
    override val superTypes = setOf(Number)
}