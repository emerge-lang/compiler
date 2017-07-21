package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.UnaryExpression
import compiler.ast.type.FunctionModifier
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.lexer.Operator
import compiler.parser.Reporting

class BoundUnaryExpression(
    override val context: CTContext,
    override val declaration: UnaryExpression,
    val original: BoundExpression<*>
) : BoundExpression<UnaryExpression> {

    override var type: BaseTypeReference? = null
        private set

    val operator = declaration.operator

    var operatorFunction: BoundFunction? = null
        private set

    override fun semanticAnalysisPhase1() = original.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(original.semanticAnalysisPhase2())

        if (original.type == null) {
            // failed to determine base type - cannot infer unary operator
            return reportings
        }

        val valueType = original.type!!

        // determine operator function
        val opFunName = operatorFunctionName(operator)

        // functions with receiver
        val receiverOperatorFuns =
            context.resolveAnyFunctions(opFunName)
                .filterAndSortByMatchForInvocationTypes(valueType, emptyList())
                .filter { FunctionModifier.OPERATOR in it.declaration.modifiers }

        operatorFunction = receiverOperatorFuns.firstOrNull()

        if (operatorFunction == null) {
            reportings.add(Reporting.error("Unary operator $operator (function $opFunName) not declared for type $valueType", declaration.sourceLocation))
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return original.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return original.findWritesBeyond(boundary)

        // unary operators are readonly by definition; the check for that happens inside the corresponding BoundFunction
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "unary" + op.name[0].toUpperCase() + op.name.substring(1).toLowerCase()
}