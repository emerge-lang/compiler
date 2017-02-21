package compiler.ast.type

val Decimal = object : BaseType {
    override val impliedModifier = TypeModifier.IMMUTABLE
    override val simpleName = "Decimal"
    override val superTypes = setOf(Number)
}