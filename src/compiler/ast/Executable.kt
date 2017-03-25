package compiler.ast

import compiler.binding.context.CTContext

/**
 * Something that can be executed. All expressions are executable (because executing an expression means evaluating
 * it within a certain context)
 *
 * @param BoundType The type that binding this code to a [CTContext] yields
 */
interface Executable<out BoundType> : Bindable<BoundType>
{
    /**
     * Communicates changes the [Executable] applies any changes to its enclosing scope (e.g. a variable declaration declares a new
     * variable)
     * @return A [CTContext] derived from the given one, with all the necessary changes applied.
     * TODO: move this to BoundExecutable
     */
    fun modified(context: CTContext): CTContext = context
}