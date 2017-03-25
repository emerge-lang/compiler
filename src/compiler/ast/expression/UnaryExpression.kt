package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.Function
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.ast.type.FunctionModifier
import compiler.binding.type.Any
import compiler.lexer.Operator
import compiler.lexer.SourceLocation

class UnaryExpression(val operator: Operator, val valueExpression: Expression): Expression
{
    override val sourceLocation = valueExpression.sourceLocation

    override fun determineType(context: CTContext): BaseTypeReference {
        return getOperatorFunction(context)?.returnType ?: Any.baseReference(context)
    }

    /**
     * Attempts to resolve the operator function in the given context.
     *
     * @return The operator function to use to evaluate this expression or null the given context does not contain
     *         a suitable function.
     */
    private fun getOperatorFunction(context: CTContext): Function? {
        val valueType = valueExpression.determineType(context)

        val opFunName = "unary" + operator.name[0].toUpperCase() + operator.name.substring(1).toLowerCase()

        // functions with receiver
        val receiverOperatorFuns =
            context.resolveAnyFunctions(opFunName)
            .filterAndSortByMatchForInvocationTypes(valueType, emptyList())
            .filter { FunctionModifier.OPERATOR in it.declaration.modifiers }

        return receiverOperatorFuns.firstOrNull()
    }
}