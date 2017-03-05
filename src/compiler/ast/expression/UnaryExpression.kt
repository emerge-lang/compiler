package compiler.ast.expression

import compiler.ast.context.CTContext
import compiler.ast.context.Function
import compiler.ast.type.BaseTypeReference
import compiler.ast.type.FunctionModifier
import compiler.lexer.Operator

class UnaryExpression(val operator: Operator, val valueExpression: Expression): Expression
{
    override fun determineType(context: CTContext): BaseTypeReference {
        return getOperatorFunction(context)?.returnType ?: compiler.ast.type.Any.baseReference(context)
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
        val receiverOperatorFuns = context.resolveAnyFunctions(opFunName, valueType.baseType)
            .filter { FunctionModifier.OPERATOR in it.declaration.modifiers }
            .filter { it.declaration.parameters.parameters.isEmpty() }

        return receiverOperatorFuns.firstOrNull()
    }
}