package compiler.binding.expression

import compiler.ast.expression.InvocationExpression
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
) : BoundExpression<InvocationExpression> {
    override var type: BaseTypeReference? = null
        private set

    fun semanticAnalysisPhase1(): Collection<Reporting> {
        // TODO: call semantic analysis on all sub-expression (catch typos in casts)
        return emptySet()
    }

    fun semanticAnalysisPhase2(): Collection<Reporting> {
        // TODO: invoke phase 2 on all sub-expressions

        // TODO: determine the function to be invoked.
        // in case of ambiguity: report an error

        // TODO: determine evaluation type from the resolved function to invoke
        // in case of ambiguity: do not attempt to infer or guess the return type.
        this.type = compiler.binding.type.Any.baseReference(context)

        // TODO: determine type of invocation: static dispatch or dynamic dispatch

        return emptySet()
    }

    fun semanticAnalysisPhase3(): Collection<Reporting> {
        // TODO: invoke semantic analysis on all sub-expressions

        return emptySet()
    }

    private fun bindTo_staticDispatch_withoutReceiver(
            context: CTContext,
            functionName: String,
            boundParameterValueExprs: List<BoundExpression<*>>,
            reportings: MutableCollection<Reporting>
    ): BindingResult<StaticDispatchInvocationExpression>
    {
        // attempt to resolve standalone function
        val functions = context.resolveAnyFunctions(functionName)
                .filter { it.receiverType == null }

        if (functions.isEmpty()) {
            reportings.add(Reporting.error("Function $functionName is not defined", sourceLocation))
        }

        val bestMatch = functions
                .filterAndSortByMatchForInvocationTypes(null, boundParameterValueExprs.map(BoundExpression<*>::type))
                .firstOrNull()

        return BindingResult(
                StaticDispatchInvocationExpression(
                        context,
                        this,
                        functionName,
                        bestMatch,
                        BoundNullLiteralExpression.getInstance(context, sourceLocation),
                        boundParameterValueExprs
                ),
                reportings
        )
    }

    private fun bindTo_staticDispatch_withReceiver(
            context: CTContext,
            receiverExpr: BoundExpression<*>,
            functionName: String,
            boundParameterValueExprs: List<BoundExpression<*>>,
            reportings: MutableCollection<Reporting>
    ): BindingResult<StaticDispatchInvocationExpression>
    {
        val receiverType = receiverExpr.type ?: compiler.binding.type.Any.baseReference(context).nullable()

        // attempt to resolve extension function
        val functionsByName = context.resolveAnyFunctions(functionName)

        if (functionsByName.isEmpty()) {
            reportings.add(Reporting.error("Function $functionName is not defined", sourceLocation))
        }

        val forReceiverType = functionsByName
                .filter { it.receiverType != null }
                .filter { receiverType isAssignableTo it.receiverType!! }

        // receiverType is genuine and no functions are found; this is an error
        // otherwise, the error would be consecutive
        if (forReceiverType.isEmpty() && receiverExpr.type != null) {
            reportings.add(Reporting.error("Function $functionName is not defined on type $receiverType", sourceLocation))
        }

        val bestMatch = forReceiverType
                .filterAndSortByMatchForInvocationTypes(receiverType, boundParameterValueExprs.map(BoundExpression<*>::type))
                .firstOrNull()

        return BindingResult(
                StaticDispatchInvocationExpression(
                        context,
                        this,
                        functionName,
                        bestMatch,
                        receiverExpr,
                        boundParameterValueExprs
                ),
                reportings
        )
    }
}