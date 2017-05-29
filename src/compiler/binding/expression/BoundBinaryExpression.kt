package compiler.binding.expression

import compiler.ast.expression.*
import compiler.ast.type.FunctionModifier
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.parser.Reporting

class BoundBinaryExpression(
    override val context: CTContext,
    override val declaration: BinaryExpression,
    val leftHandSide: BoundExpression<*>,
    val operator: Operator,
    val rigthHandSide: BoundExpression<*>
) : BoundExpression<BinaryExpression> {

    private val hiddenInvocation: BoundInvocationExpression = InvocationExpression(
            MemberAccessExpression(
                    leftHandSide.declaration as Expression<*>,
                    IdentifierToken(operatorFunctionName(operator), declaration.op.sourceLocation)
            ),
            listOf(rigthHandSide.declaration as Expression<*>)
    )
            .bindTo(context)

    override val type: BaseTypeReference?
        get() = hiddenInvocation.type

    override fun semanticAnalysisPhase1() = hiddenInvocation.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        reportings.addAll(hiddenInvocation.semanticAnalysisPhase2())

        val opFn = hiddenInvocation.dispatchedFunction
        if (opFn != null) {
            if (FunctionModifier.OPERATOR !in opFn.modifiers) {
                reportings.add(Reporting.error("Function $opFn is missing the operator modifier", declaration.sourceLocation))
            }
        }

        return reportings
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "op" + op.name[0].toUpperCase() + op.name.substring(1).toLowerCase()
}