package compiler.binding.expression

import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken
import compiler.parser.Reporting

class BoundInvocationExpression(
    override val context: CTContext,
    override val declaration: InvocationExpression,
    /** The receiver expression; is null if not specified in the source */
    val receiverExpression: BoundExpression<*>?,
    val functionNameToken: IdentifierToken,
    val parameterExpressions: List<BoundExpression<*>>
) : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression> {
    override var type: BaseTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> =
        (receiverExpression?.semanticAnalysisPhase1() ?: emptySet()) + parameterExpressions.flatMap(BoundExpression<*>::semanticAnalysisPhase1)

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (receiverExpression != null) reportings.addAll(receiverExpression.semanticAnalysisPhase2())
        parameterExpressions.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }

        // determine the function to be invoked
        val functionCandidates = semanticPhase3_determineFunction()
        if (functionCandidates.isEmpty()) {
            reportings.add(Reporting.unresolvableFunction(this))
        }

        val function = functionCandidates.firstOrNull()

        // the resolved function yields the evaluation type
        if (function != null) {
            reportings.addAll(function.semanticAnalysisPhase2())
            type = function.returnType
        }

        // TODO: determine type of invocation: static dispatch or dynamic dispatch

        return reportings
    }

    /**
     * Attempts to resolve all candidates for the invocation. If the receiver type cannot be resolved, assumes `Any?`
     */
    private fun semanticPhase3_determineFunction(): List<BoundFunction> {
        if (receiverExpression == null) {
            return context.resolveAnyFunctions(functionNameToken.value)
                    .filter { it.receiverType == null }
                    .filterAndSortByMatchForInvocationTypes(null, parameterExpressions.map(BoundExpression<*>::type))
        } else {
            val receiverType = receiverExpression.type ?: compiler.binding.type.Any.baseReference(context).nullable()
            return context.resolveAnyFunctions(functionNameToken.value)
                .filterAndSortByMatchForInvocationTypes(
                    receiverType,
                    parameterExpressions.map { it.type }
                )
        }
    }

    fun semanticAnalysisPhase3(): Collection<Reporting> {
        // TODO: invoke semantic analysis on all sub-expressions

        return emptySet()
    }
}