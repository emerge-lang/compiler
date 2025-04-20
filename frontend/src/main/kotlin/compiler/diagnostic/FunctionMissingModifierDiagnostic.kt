package compiler.diagnostic

import compiler.ast.Executable
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundInvocationExpression

/**
 * TODO:
 * * rename to FunctionMissingAttributeDiagnostic
 */
data class FunctionMissingModifierDiagnostic(
    val function: BoundFunction,
    val usageRequiringModifier: Executable,
    val missingAttribute: String,
) : Diagnostic(
    Severity.ERROR,
    "Missing attribute \"${missingAttribute}\" on function ${function.canonicalName}",
    usageRequiringModifier.span,
), InvocationCandidateNotApplicableDiagnostic {
    override fun toString() = super.toString() + "\ndeclared without this modifier here:\n${function.declaredAt}"

    override val inapplicabilityHint: SourceHint
        get() = SourceHint(function.declaredAt, "missing attribute $missingAttribute")
    override fun asDiagnostic() = this

    companion object {
        fun requireOperatorModifier(
            subject: BoundInvocationExpression,
            requirer: BoundExecutable<*>,
            diagnosis: Diagnosis,
        ) {
            val operatorFn = subject.functionToInvoke ?: return
            if (!operatorFn.attributes.isDeclaredOperator) {
                diagnosis.functionIsMissingAttribute(
                    operatorFn,
                    requirer.declaration,
                    "operator",
                )
            }
        }
    }
}