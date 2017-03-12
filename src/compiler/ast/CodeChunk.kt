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
        val reportings = mutableListOf<Reporting>()
        statements.forEach {
            reportings.addAll(it.validate(context))
        }
        return reportings
    }
}