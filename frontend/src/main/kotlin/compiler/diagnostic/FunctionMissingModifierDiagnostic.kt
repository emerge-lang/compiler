package compiler.diagnostic

import compiler.ast.Executable
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundInvocationExpression

data class FunctionMissingModifierDiagnostic(
    val function: BoundFunction,
    val usageRequiringModifier: Executable,
    val missingAttribute: String,
) : Diagnostic(
    Diagnostic.Level.ERROR,
    "Missing modifier \"${missingAttribute}\" on function ${function.canonicalName}",
    usageRequiringModifier.span,
) {
    override fun toString() = super.toString() + "\ndeclared without this modifier here:\n${function.declaredAt}"

    companion object {
        fun requireOperatorModifier(
            subject: BoundInvocationExpression,
            requirer: BoundExecutable<*>,
            diagnosis: Diagnosis,
        ) {
            val operatorFn = subject.functionToInvoke ?: return
            if (!operatorFn.attributes.isDeclaredOperator) {
                diagnosis.add(
                    Diagnostic.functionIsMissingAttribute(
                        operatorFn,
                        requirer.declaration,
                        "operator",
                    )
                )
            }
        }
    }
}