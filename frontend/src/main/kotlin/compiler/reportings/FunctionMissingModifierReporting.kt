package compiler.reportings

import compiler.ast.Executable
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundInvocationExpression

data class FunctionMissingModifierReporting(
    val function: BoundFunction,
    val usageRequiringModifier: Executable,
    val missingAttribute: String,
) : Reporting(
    Reporting.Level.ERROR,
    "Missing modifier \"${missingAttribute::class.simpleName?.lowercase()}\" on function ${function.canonicalName}",
    usageRequiringModifier.span,
) {
    override fun toString() = super.toString() + "\ndeclared without this modifier here:\n${function.declaredAt}"

    companion object {
        fun requireOperatorModifier(
            subject: BoundInvocationExpression,
            requirer: BoundExecutable<*>,
            reportings: MutableCollection<in Reporting>,
        ) {
            val operatorFn = subject.functionToInvoke ?: return
            if (!operatorFn.attributes.isDeclaredOperator) {
                reportings.add(
                    Reporting.functionIsMissingAttribute(
                        operatorFn,
                        requirer.declaration,
                        "operator",
                    )
                )
            }
        }
    }
}