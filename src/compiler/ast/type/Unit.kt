package compiler.ast.type

val Unit = object : BaseType {
    override val simpleName = "Unit"
    override val superTypes = setOf(Any)
}