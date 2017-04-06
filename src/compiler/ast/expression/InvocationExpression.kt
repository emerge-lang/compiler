package compiler.ast.expression

import compiler.InternalCompilerError
import compiler.ast.Executable
import compiler.binding.BindingResult
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.expression.BoundNullLiteralExpression
import compiler.binding.expression.StaticDispatchInvocationExpression
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.lexer.SourceLocation
import compiler.parser.Reporting
import java.lang.UnsupportedOperationException

class InvocationExpression(
    /**
     * The target of the invocation. e.g.:
     * * `doStuff()` => `IdentifierExpression(doStuff)`
     * * `obj.doStuff()` => `MemberAccessExpression(obj, doStuff)`
     */
    val functionExpression: Expression<*>,
    val parameterExprs: List<Expression<*>>
) : Expression<BoundInvocationExpression>, Executable<BoundInvocationExpression> {
    override val sourceLocation: SourceLocation = when(functionExpression) {
        is MemberAccessExpression -> functionExpression.memberName.sourceLocation
        else -> functionExpression.sourceLocation
    }

    override fun bindTo(context: CTContext): BindingResult<BoundInvocationExpression> {
        val reportings = mutableListOf<Reporting>()

        // bind all the parameters
        val boundParameterValueExprs = parameterExprs.map {
            val br = it.bindTo(context)
            reportings.addAll(br.reportings)
            br.bound
        }

        // decide the kind of dispatch
        if (functionExpression is MemberAccessExpression) {
            val receiverExprBR = functionExpression.valueExpression.bindTo(context)
            reportings.addAll(receiverExprBR.reportings)

            // TODO: member functions

            return bindTo_staticDispatch_withReceiver(
                context,
                receiverExprBR.bound,
                functionExpression.memberName.value,
                boundParameterValueExprs,
                reportings
            )
        }
        else if (functionExpression is IdentifierExpression) {
            // TODO: function types => variable of function type

            return bindTo_staticDispatch_withoutReceiver(
                context,
                functionExpression.identifier.value,
                boundParameterValueExprs,
                reportings
            )
        }
        else throw InternalCompilerError("What the heck is going on?? The parser should never have allowed this!")
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