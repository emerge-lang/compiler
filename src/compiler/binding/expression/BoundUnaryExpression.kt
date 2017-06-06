package compiler.binding.expression

import compiler.ast.expression.UnaryExpression
import compiler.ast.type.FunctionModifier
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundUnaryExpression(
    override val context: CTContext,
    override val declaration: UnaryExpression,
    val original: BoundExpression<*>
) : BoundExpression<UnaryExpression> {

    override var type: BaseTypeReference? = null
        private set

    override val isReadonly: Boolean?
        get() = original.isReadonly

    val operator = declaration.operator

    override fun semanticAnalysisPhase1() = original.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(original.semanticAnalysisPhase2())

        if (original.type == null) {
            // failed to determine base type - cannot infer unary operator
            return reportings
        }

        val valueType = original.type!!

        val operatorFunction: BoundFunction?

        // determine operator function
        val opFunName = "unary" + declaration.operator.name[0].toUpperCase() + declaration.operator.name.substring(1).toLowerCase()

        // functions with receiver
        val receiverOperatorFuns =
            context.resolveAnyFunctions(opFunName)
                .filterAndSortByMatchForInvocationTypes(valueType, emptyList())
                .filter { FunctionModifier.OPERATOR in it.declaration.modifiers }

        operatorFunction = receiverOperatorFuns.firstOrNull()

        if (operatorFunction == null) {
            reportings.add(Reporting.error("Unary operator $operator not declared for type $valueType", declaration.sourceLocation))
        }

        return reportings
    }
}