package compiler.ast

import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation

/**
 * Something that can be executed. All expressions are executable (because executing an expression means evaluating
 * it within a certain context)
 *
 * @param BoundType The type that binding this code to a [CTContext] yields
 */
interface Executable<out BoundType : BoundExecutable<*>> : Bindable<BoundType> {
    val sourceLocation: SourceLocation
}