package compiler.ast

import compiler.ast.context.CTContext
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
}