package compiler.binding

import compiler.ast.Executable
import compiler.binding.context.CTContext

interface BoundExecutable<out ASTType> {
    val context: CTContext

    val declaration: ASTType

    /**
     * Communicates changes the [Executable] applies any changes to its enclosing scope (e.g. a variable declaration declares a new
     * variable)
     * @return A [CTContext] derived from the given one, with all the necessary changes applied.
     */
    fun modified(context: CTContext): CTContext = context
}