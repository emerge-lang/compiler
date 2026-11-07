package compiler.ast.expression

import compiler.ast.AstSemanticOperator
import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundRangeExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import io.github.tmarsteel.emerge.backend.RANGE_TO_EXCLUSIVE_FN_NAME

/**
 * `start..<endExclusive`. Evaluates to `start.rangeToExclusive(endExclusive)`, except where the surrounding
 * syntax handles ranges itself, e.g. `array[start..<endExclusive]` (see [AstIndexAccessExpression]).
 */
class AstRangeExpression(
    val start: Expression,
    val operator: AstSemanticOperator,
    val endExclusive: Expression,
) : Expression {
    override val span = start.span .. endExclusive.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundRangeExpression {
        val generatedSpan = operator.token.span.deriveGenerated()
        val hiddenInvocation = InvocationExpression(
            MemberAccessExpression(
                start,
                OperatorToken(Operator.DOT, generatedSpan),
                IdentifierToken(RANGE_TO_EXCLUSIVE_FN_NAME, generatedSpan),
            ),
            null,
            listOf(endExclusive),
            span,
        ).bindTo(context)

        return BoundRangeExpression(context, this, hiddenInvocation)
    }
}
