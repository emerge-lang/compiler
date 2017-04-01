package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.BoundFunction
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.ast.type.FunctionModifier
import compiler.binding.BindingResult
import compiler.binding.expression.BoundBinaryExpression
import compiler.binding.type.Any
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.Reporting

class BinaryExpression(
    val first: Expression<*>,
    val op: OperatorToken,
    val second: Expression<*>
) : Expression<BoundBinaryExpression> {
    override val sourceLocation = first.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundBinaryExpression> {
        val reportings = mutableListOf<Reporting>()

        val firstBR = first.bindTo(context)
        val secondBR = second.bindTo(context)

        reportings.addAll(firstBR.reportings)
        reportings.addAll(secondBR.reportings)

        val typeFirst = firstBR.bound.type
        val typeSecond = secondBR.bound.type

        // determine operator function
        val opFunName = operatorFunctionName(op.operator)

        val opFn =
            context.resolveAnyFunctions(opFunName)
                .filterAndSortByMatchForInvocationTypes(typeFirst, listOf(typeSecond))
                .filter { FunctionModifier.OPERATOR in it.declaration.modifiers}
                .firstOrNull()

        if (opFn == null && typeFirst != null && typeSecond != null) {
            reportings.add(Reporting.error("Operator ${operatorFunctionName(op.operator)}($typeSecond) is not defined on type $typeFirst", op))
        }

        return BindingResult(
            BoundBinaryExpression(
                context,
                this,
                opFn?.returnType,
                firstBR.bound,
                op.operator,
                secondBR.bound,
                opFn
            ),
            reportings
        )
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "op" + op.name[0].toUpperCase() + op.name.substring(1).toLowerCase()
}