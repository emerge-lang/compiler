package compiler.ast.type

val Number = object : BaseType {
    override val impliedModifier = TypeModifier.IMMUTABLE
    override val simpleName = "Number"
}