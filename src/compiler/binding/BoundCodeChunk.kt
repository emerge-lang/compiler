package compiler.binding

import compiler.ast.CodeChunk
import compiler.binding.context.CTContext

class BoundCodeChunk(
    /**
     * Context that applies to the first statement; derivatives are stored within the statements themselves
     */
    override val context: CTContext,

    override val declaration: CodeChunk
) : BoundExecutable<CodeChunk>