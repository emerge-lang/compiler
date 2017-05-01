package compiler.ast

import compiler.binding.BoundCodeChunk
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation

/**
 * A piece of executable code
 */
class CodeChunk(
    val statements: List<Executable<*>>
) : Executable<BoundCodeChunk> {
    override val sourceLocation: SourceLocation = statements.firstOrNull()?.sourceLocation ?: SourceLocation.UNKNOWN

    override fun bindTo(context: CTContext) = BoundCodeChunk(context, this)
}