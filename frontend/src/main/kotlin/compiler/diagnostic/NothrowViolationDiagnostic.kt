package compiler.diagnostic

import compiler.ast.AstThrowExpression
import compiler.ast.expression.AstCastExpression
import compiler.ast.expression.NotNullExpression
import compiler.binding.BoundFunction
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.binding.expression.BoundInvocationExpression
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.lexer.Span

open class NothrowViolationDiagnostic(
    severity: Severity,
    message: String,
    sourceLocation: Span,
) : Diagnostic(severity, message, sourceLocation) {
    class NotNullAssertion(
        val assertion: NotNullExpression,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationDiagnostic(
        Severity.ERROR,
        "Cannot use !! in in nothrow $boundary; it can throw a NullPointerError",
        assertion.notNullOperator.span,
    )

    class ThrowingInvocation(
        val invocation: BoundInvocationExpression,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationDiagnostic(
        Severity.ERROR,
        "Cannot invoke possibly-throwing function ${invocation.functionToInvoke!!.canonicalName} in nothrow $boundary",
        invocation.declaration.span,
    )

    class ThrowStatement(
        val statement: AstThrowExpression,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationDiagnostic(
        Severity.ERROR,
        "Cannot throw from nothrow $boundary",
        statement.span,
    )

    class StrictCast(
        val castExpression: AstCastExpression,
        val boundary: SideEffectBoundary,
    ) : NothrowViolationDiagnostic(
        Severity.ERROR,
        "Cannot force-cast in nothrow $boundary; casts can always throw a CastError. Use ${Keyword.AS.text}${Operator.QUESTION_MARK.text} or ${Keyword.INSTANCEOF.text} in an ${Keyword.IF.text}-expression instead.",
        castExpression.asToken.span,
    )

    sealed interface SideEffectBoundary {
        val nothrowDeclaredAt: Span
        class Function(
            val fn: BoundFunction
        ) : SideEffectBoundary {
            override val nothrowDeclaredAt get() = fn.attributes.firstNothrowAttribute!!.sourceLocation

            override fun toString() = when (fn) {
                is BoundClassConstructor -> "constructor of ${fn.classDef.simpleName}"
                is BoundClassDestructor -> "destructor of ${fn.classDef.simpleName}"
                else -> "function ${fn.name}"
            }
        }
    }
}