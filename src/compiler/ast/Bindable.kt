package compiler.ast

import compiler.binding.BindingResult
import compiler.binding.context.CTContext

interface Bindable<out BoundType> {
    /**
     * Binds the code to the given [CTContext], validating it and yielding an instance of the [BoundType].
     */
    fun bindTo(context: CTContext): BindingResult<BoundType>
}