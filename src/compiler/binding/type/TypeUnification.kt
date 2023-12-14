package compiler.binding.type

import compiler.ast.type.TypeVariance
import java.util.IdentityHashMap

class TypeUnification private constructor (
    private val _left: IdentityHashMap<String, BoundTypeArgument>,
    private val _right: IdentityHashMap<String, BoundTypeArgument>,
) {
    val left: Map<String, BoundTypeArgument> = _left
    val right: Map<String, BoundTypeArgument> = _right

    fun plusLeft(param: String, type: BoundTypeArgument): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = TypeUnification(
            _left.clone() as IdentityHashMap<String, BoundTypeArgument>,
            _right, // doesn't get modified here
        )
        bindInPlace(clone._left, param, type)
        return clone
    }

    fun plusRight(param: String, type: BoundTypeArgument): TypeUnification {
        @Suppress("UNCHECKED_CAST")
        val clone = TypeUnification(
            _left, // doesn't get modified here
            _right.clone() as IdentityHashMap<String, BoundTypeArgument>,
        )
        bindInPlace(clone._right, param, type)
        return clone
    }

    override fun toString(): String {
        if (left.isEmpty() && right.isEmpty()) {
            return "EMPTY"
        }

        fun sideToString(side: Map<String, BoundTypeArgument>) = side.entries.joinToString(
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

        private fun bindInPlace(map: IdentityHashMap<String, BoundTypeArgument>, param: String, type: BoundTypeArgument) {
            map.compute(param) { _, previousBinding ->
                previousBinding?.closestCommonSupertypeWith(type)
                    ?.let {
                        if (it is BoundTypeArgument) it else BoundTypeArgument(it.context, null, TypeVariance.UNSPECIFIED, it)
                    }
                    ?: type
            }
        }
    }
}