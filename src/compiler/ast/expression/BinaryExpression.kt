package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.BoundFunction
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.ast.type.FunctionModifier
import compiler.binding.type.Any
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.Reporting

class BinaryExpression(
    val first: Expression,
    val op: OperatorToken,
    val second: Expression
) : Expression {
    override val sourceLocation = first.sourceLocation

    override fun determineType(context: CTContext): BaseTypeReference? {
        return getOperatorFunction(context)?.returnType
    }

    override fun validate(context: CTContext): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        reportings.addAll(first.validate(context))
        reportings.addAll(second.validate(context))

        val typeFirst = first.determineType(context)
        val typeSecond = second.determineType(context)

        val opFn = getOperatorFunction(context)
        if (opFn == null && typeFirst != null && typeSecond != null) {
            reportings.add(Reporting.error("Operator ${operatorFunctionName(op.operator)}($typeSecond) is not defined on type $typeFirst", op))
        }

        return reportings
    }

    /**
     * Attempts to resolve the operator function in the given context.
     *
     * @return The operator function to use to evaluate this expression or null the given context does not contain
     *         a suitable function.
     */
    private fun getOperatorFunction(context: CTContext): BoundFunction? {
        val typeFirst = first.determineType(context) ?: return null
        val typeSecond: BaseTypeReference = second.determineType(context) ?: Any.baseReference(context)

        val opFunName = operatorFunctionName(op.operator)

        val receiverOperatorFuns =
            context.resolveAnyFunctions(opFunName)
            .filterAndSortByMatchForInvocationTypes(typeFirst, listOf(typeSecond))
            .filter { FunctionModifier.OPERATOR in it.declaration.modifiers}

        return receiverOperatorFuns.firstOrNull()
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "op" + op.name[0].toUpperCase() + op.name.substring(1).toLowerCase()
}