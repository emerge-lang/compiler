package compiler.binding.impurity

fun interface ImpurityVisitor {
    fun visit(impurity: Impurity)
}