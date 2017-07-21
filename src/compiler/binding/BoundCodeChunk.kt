package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.CodeChunk
import compiler.ast.Executable
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

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        if (statements == null) throw InternalCompilerError("Illegal state: invoke this function after semantic analysis phase 3 is completed.")

        return statements!!.flatMap { it.findReadsBeyond(boundary) }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        if (statements == null) throw InternalCompilerError("Illegal state: invoke this function after semantic analysis phase 3 is completed.")

        return statements!!.flatMap { it.findWritesBeyond(boundary) }
    }
}