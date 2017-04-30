package compiler.binding

import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement
) : BoundExecutable<ReturnStatement> {
    val expression = declaration.expression.bindTo(context)

    var returnType: BaseTypeReference? = null
        private set

    fun semanticAnalysisPhase1(): Collection<Reporting> {
        // invoke this method on the return statement
        val reportings = expression.semanticAnalysisPhase1()
        returnType = expression.type

        return reportings
    }
}