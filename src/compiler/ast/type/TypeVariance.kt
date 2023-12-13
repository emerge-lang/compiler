package compiler.ast.type

enum class TypeVariance {
    UNSPECIFIED,
    IN,
    OUT,
    ;

    override fun toString() = when(this) {
        UNSPECIFIED -> "<${name.lowercase()}>"
        else -> name.lowercase()
    }
}