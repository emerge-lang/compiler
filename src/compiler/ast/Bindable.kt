package compiler.ast

import compiler.binding.context.CTContext

interface Bindable<out BoundType> {
    /**
     * Binds the code to the given [CTContext], yielding an INSTANCE of the [BoundType].
     */
    fun bindTo(context: CTContext): BoundType
}