package compiler.ast.types

enum class TypeModifier {
    MUTABLE,
    READONLY,
    IMMUTABLE;

    fun isAssignableTo(targetModifier: TypeModifier): Boolean =
        this == targetModifier
            ||
        when (this) {
            MUTABLE, IMMUTABLE -> targetModifier == READONLY
            READONLY -> false
        }
}
