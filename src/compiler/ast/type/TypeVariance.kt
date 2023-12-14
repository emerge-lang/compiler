package compiler.ast.type

enum class TypeVariance {
    /** rename to invariant? */
    UNSPECIFIED,
    IN,
    OUT,
    ;

    override fun toString() = when(this) {
        UNSPECIFIED -> "<${name.lowercase()}>"
        else -> name.lowercase()
    }
}