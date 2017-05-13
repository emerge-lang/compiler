package compiler.ast.expression

import compiler.ast.type.FunctionModifier
import compiler.binding.BindingResult
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundUnaryExpression
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.lexer.Operator
import compiler.parser.Reporting

class UnaryExpression(val operator: Operator, val valueExpression: Expression<*>): Expression<BoundUnaryExpression>
{
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundUnaryExpression> {
        val reportings = mutableSetOf<Reporting>()

        // determine type without operator applied
        val valueExprBR = valueExpression.bindTo(context)
        val valueType = valueExprBR.bound.type

        val operatorFunction: BoundFunction?
        if (valueType != null) {
            // determine operator function
            val opFunName = "unary" + operator.name[0].toUpperCase() + operator.name.substring(1).toLowerCase()

            // functions with receiver
            val receiverOperatorFuns =
                context.resolveAnyFunctions(opFunName)
                    .filterAndSortByMatchForInvocationTypes(valueType, emptyList())
                    .filter { FunctionModifier.OPERATOR in it.declaration.modifiers }

            operatorFunction = receiverOperatorFuns.firstOrNull()

            if (operatorFunction == null) {
                reportings.add(Reporting.error("Unary operator $operator not declared for type $valueType", valueExpression.sourceLocation))
            }
        }
        else operatorFunction = null

        return BindingResult(
            BoundUnaryExpression(
                context,
                this,
                operatorFunction?.receiverType,
                valueExprBR.bound
            ),
            reportings
        )
    }
}