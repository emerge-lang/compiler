package compiler.binding

import compiler.ast.CodeChunk
import compiler.binding.context.CTContext
import compiler.parser.Reporting

class BoundCodeChunk(
    /**
     * Context that applies to the leftHandSide statement; derivatives are stored within the statements themselves
     */
    override val context: CTContext,

    override val declaration: CodeChunk
) : BoundExecutable<CodeChunk> {

    /** The bound statements of this code; must not be null after semantic analysis is done */
    var statements: List<BoundExecutable<*>>? = null
        private set

    override var isReadonly: Boolean? = null
        private set

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        var currentContext = context
        val boundStatements = mutableListOf<BoundExecutable<*>>()

        for (astStatement in declaration.statements) {
            val boundStatement = astStatement.bindTo(currentContext)

            reportings += boundStatement.semanticAnalysisPhase1()
            reportings += boundStatement.semanticAnalysisPhase2()
            reportings += boundStatement.semanticAnalysisPhase3()

            boundStatements.add(boundStatement)
            currentContext = boundStatement.modified(currentContext)
        }

        this.statements = boundStatements

        return reportings
    }
}