package compiler.ast.types

enum class TypeModifier {
    MUTABLE,
    READONLY,
    IMMUTABLE;

    fun isCompatibleWith(other: TypeModifier): Boolean = when(this) {
        MUTABLE, IMMUTABLE -> other == this
        READONLY -> true
    }
}