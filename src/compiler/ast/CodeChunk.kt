package compiler.ast

import compiler.ast.context.CTContext
import compiler.parser.Reporting

/**
 * A piece of executable code
 */
class CodeChunk(
    val statements: List<Executable>
) : Executable {
    override fun validate(context: CTContext): Collection<Reporting> {
        /** gets reassigned for every executable that modifies the context */
        var _context = context

        val reportings = mutableListOf<Reporting>()

        statements.forEach { stmt ->
            reportings.addAll(stmt.validate(_context))
            _context = stmt.modified(_context)
        }

        return reportings
    }
}