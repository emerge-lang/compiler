package compiler.diagnostic

import compiler.ast.AstFunctionAttribute
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundInvocationExpression
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span

class FunctionMissingAttributeDiagnostic(
    val function: BoundFunction,
    attributeRequiredByUsageAt: Span,
    val attribute: AstFunctionAttribute,
    reason: String?,
) : Diagnostic(
    Severity.ERROR,
    run {
        var msg = "Function `${function.name}` missing in attribute ${attribute.attributeName.keyword.text}"
        if (reason != null) {
            msg = "$msg: $reason"
        }
        msg
    },
    attributeRequiredByUsageAt,
), InvocationCandidateNotApplicableDiagnostic {
    override fun toString() = super.toString() + "\ndeclared without at here:\n${function.declaredAt}"

    override val inapplicabilityHint: SourceHint
        get() = SourceHint(function.declaredAt, "missing attribute ${attribute.attributeName.keyword.text}")
    override fun asDiagnostic() = this

    companion object {
        fun requireOperatorAttribute(
            subject: BoundInvocationExpression,
            requirer: BoundExecutable<*>,
            diagnosis: Diagnosis,
        ) {
            val operatorFn = subject.functionToInvoke ?: return
            if (!operatorFn.attributes.isDeclaredOperator) {
                diagnosis.functionIsMissingAttribute(
                    operatorFn,
                    requirer.declaration.span,
                    AstFunctionAttribute.Operator(KeywordToken(Keyword.OPERATOR)),
                    reason = null,
                )
            }
        }
    }
}