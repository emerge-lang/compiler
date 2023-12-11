package compiler.binding.type

import java.util.IdentityHashMap

class TypeUnification private constructor (
    private val _left: IdentityHashMap<String, BoundTypeArgument>,
    private val _right: IdentityHashMap<String, BoundTypeArgument>,
) {
    val left: Map<String, BoundTypeArgument> = _left
    val right: Map<String, BoundTypeArgument> = _right

    fun plusLeft(param: String, type: BoundTypeArgument): TypeUnification {
        val clone = clone()
        check(clone._left.putIfAbsent(param, type) == null) {
            "Double binding(right) for the type parameter $param"
        }

        return clone
    }

    fun plusRight(param: String, type: BoundTypeArgument): TypeUnification {
        val clone = clone()
        check(clone._right.putIfAbsent(param, type) == null) {
            "Double binding(right) for the type parameter $param"
        }

        return clone
    }

    private fun clone() = TypeUnification(
        IdentityHashMap(left),
        IdentityHashMap(right),
    )

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
    }
}