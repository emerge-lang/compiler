package compiler.ast.expression

import compiler.ast.context.CTContext
import compiler.ast.context.Function
import compiler.ast.context.filterAndSortByMatchForInvocationTypes
import compiler.ast.type.BaseTypeReference
import compiler.ast.type.FunctionModifier
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
    private fun getOperatorFunction(context: CTContext): Function? {
        val typeFirst = first.determineType(context) ?: return null
        val typeSecond: BaseTypeReference = second.determineType(context) ?: compiler.ast.type.Any.baseReference(context)

        val opFunName = operatorFunctionName(op.operator)

        val receiverOperatorFuns =
            context.resolveAnyFunctions(opFunName)
            .filterAndSortByMatchForInvocationTypes(typeFirst, listOf(typeSecond))
            .filter { FunctionModifier.OPERATOR in it.declaration.modifiers}

        return receiverOperatorFuns.firstOrNull()
    }
}

private fun <T, R> Iterable<T>.attachMapNotNull(transform: (T) -> R): Iterable<Pair<T, R>> = map{ it to transform(it) }.filter { it.second != null }

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "op" + op.name[0].toUpperCase() + op.name.substring(1).toLowerCase()
}