package compiler.ast

import compiler.binding.context.CTContext
import compiler.parser.Reporting

/**
 * Something that can be executed. All expressions are executable (because executing an expression means evaluating
 * it within a certain context)
 */
interface Executable
{
    /**
     * Validates the executable code within the given context.
     *
     * @return Any reportings about the code validated.
     */
    fun validate(context: CTContext): Collection<Reporting> = emptySet() // TODO: remove dummy implementation when possible

    /**
     * Communicates changes the [Executable] applies any changes to its enclosing scope (e.g. a variable declaration declares a new
     * variable)
     * @return A [CTContext] derived from the given one, with all the necessary changes applied.
     */
    fun modified(context: CTContext): CTContext = context
}