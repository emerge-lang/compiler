package compiler.ast.type

/**
 * Type parameterization on the referencing side.
 * @see TypeParameter
 */
data class TypeArgument(
    val variance: TypeVariance,
    val type: TypeReference,
) {
    override fun toString(): String {
        var str = ""
        if (variance != TypeVariance.UNSPECIFIED) {
            str += variance.name.lowercase()
            str += " "
        }

        return str + type.toString()
    }
}