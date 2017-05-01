package compiler.ast

import compiler.binding.BindingResult
import compiler.binding.BoundCodeChunk
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

/**
 * A piece of executable code
 */
class CodeChunk(
    val statements: List<Executable<*>>
) : Executable<BoundCodeChunk> {
    override val sourceLocation: SourceLocation = statements.firstOrNull()?.sourceLocation ?: SourceLocation.UNKNOWN

    override fun bindTo(context: CTContext): BoundCodeChunk {
        /** gets reassigned for every executable that modifies the context */
        var _context = context

        val reportings = mutableListOf<Reporting>()

        val boundStmts = statements.map { stmt ->
            val stmtBR = stmt.bindTo(_context)
            reportings.addAll(stmtBR.reportings)
            _context = stmtBR.bound.modified(_context)
            stmtBR.bound
        }

        return BindingResult(
            BoundCodeChunk(
                context,
                this,
                boundStmts
            ),
            reportings
        )
    }
}