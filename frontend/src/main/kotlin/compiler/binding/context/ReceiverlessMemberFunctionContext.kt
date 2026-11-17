package compiler.binding.context

import compiler.binding.type.BoundTypeParameter

/**
 * The context of a member function that doesn't declare a receiver. The type parameters of the base type
 * are not available in such a function: their values belong to an object, and the function has none.
 * @param baseTypeContext the context of the base type, with its type parameters
 */
class ReceiverlessMemberFunctionContext(
    private val baseTypeContext: CTContext,
) : MutableCTContext(baseTypeContext) {
    override val allTypeParameters: Sequence<BoundTypeParameter> = emptySequence()

    override fun resolveTypeParameter(simpleName: String): BoundTypeParameter? = null

    override fun resolveTypeParameterUnavailableWithoutReceiver(simpleName: String): BoundTypeParameter? {
        return baseTypeContext.resolveTypeParameter(simpleName)
            ?: baseTypeContext.resolveTypeParameterUnavailableWithoutReceiver(simpleName)
    }
}
