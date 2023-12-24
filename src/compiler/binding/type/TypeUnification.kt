package compiler.binding.type

import java.util.IdentityHashMap

class TypeUnification private constructor (
    private val _left: IdentityHashMap<String, ResolvedTypeReference>,
    private val _right: IdentityHashMap<String, ResolvedTypeReference>,
) {
    val left: Map<String, ResolvedTypeReference> = _left
    val right: Map<String, ResolvedTypeReference> = _right

    fun plusLeft(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = TypeUnification(
            _left.clone() as IdentityHashMap<String, ResolvedTypeReference>,
            _right, // doesn't get modified here
        )
        bindInPlace(clone._left, param, binding)
        return clone
    }

    fun plusRight(
        param: String,
        binding: ResolvedTypeReference,
    ): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = TypeUnification(
            _left, // doesn't get modified here
            _right.clone() as IdentityHashMap<String, ResolvedTypeReference>,
        )
        bindInPlace(clone._right, param, binding)
        return clone
    }

    override fun toString(): String {
        if (left.isEmpty() && right.isEmpty()) {
            return "EMPTY"
        }

        fun sideToString(side: Map<String, ResolvedTypeReference>) = side.entries.joinToString(
            prefix = "[",
            transform = { (name, value) -> "$name = $value" },
            separator = ", ",
            postfix = "]",
        )

        return "Left:${sideToString(left)} Right:${sideToString(right)}"
    }

    companion object {
        val EMPTY = TypeUnification(IdentityHashMap(), IdentityHashMap())

        fun fromInherent(type: RootResolvedTypeReference): TypeUnification {
            return TypeUnification(
                _left = type.baseType.parameters.zip(type.arguments) { parameter, argument ->
                    parameter.name.value to argument
                }.toMap(IdentityHashMap()),
                _right = IdentityHashMap(),
            )
        }

        private fun bindInPlace(
            map: IdentityHashMap<String, ResolvedTypeReference>,
            param: String,
            binding: ResolvedTypeReference,
        ) {
            map.compute(param) { _, previousBinding ->
                when {
                    previousBinding is BoundTypeArgument -> previousBinding
                    binding is BoundTypeArgument -> binding
                    else -> previousBinding?.closestCommonSupertypeWith(binding) ?: binding
                }
            }
        }
    }
}