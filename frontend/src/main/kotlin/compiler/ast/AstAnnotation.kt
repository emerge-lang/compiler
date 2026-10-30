package compiler.ast

import compiler.binding.BoundAnnotation
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.Span

class AstAnnotation(
    val expression: Expression,
    val span: Span,
) {
    fun bindTo(context: ExecutionScopedCTContext): BoundAnnotation {
        return BoundAnnotation(this, expression.bindTo(context))
    }
}