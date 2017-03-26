package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.ast.type.TypeReference
import compiler.binding.BindingResult
import compiler.binding.BoundExecutable
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundNotNullExpression
import compiler.lexer.OperatorToken

/** A not-null enforcement expression created by the !! operator */
class NotNullExpression(
    val nullableExpression: Expression<*>,
    val notNullOperator: OperatorToken
) : Expression<BoundNotNullExpression>, Executable<BoundNotNullExpression>
{
    override val sourceLocation = nullableExpression.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundNotNullExpression> {
        val valueExprBinding = nullableExpression.bindTo(context)

        return BindingResult(
            BoundNotNullExpression(
                context,
                this,
                valueExprBinding.bound.type?.nonNull(),
                valueExprBinding.bound
            ),
            valueExprBinding.reportings
        )

        // TODO: reporting on superfluous notnull when nullableExpression.type.nullable == false
    }
}