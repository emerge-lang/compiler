package compiler.ast.type

import compiler.ast.FunctionDeclaration
import compiler.ast.context.CTContext

/**
 * Base type are classes, interfaces, enums, built-in type
 */
interface BaseType {
    val impliedModifier: TypeModifier
        get() = TypeModifier.MUTABLE

    val simpleName: String
        get() = javaClass.simpleName

    // TODO: infer this from declaring module and simpleName
    val fullyQualifiedName: String
        get() = simpleName

    val reference: TypeReference
        get() = TypeReference(fullyQualifiedName, false, impliedModifier)

    val baseReference: (CTContext) -> BaseTypeReference
        get() = { ctx -> BaseTypeReference(reference, ctx, this) }

    val superTypes: Set<BaseType>
        get() = emptySet()

    /** @return Whether this type is the same as or a subtype of the given type. */
    infix fun isSubtypeOf(other: BaseType): Boolean {
        if (other === this) return true

        return superTypes.map { it.isSubtypeOf(other) }.fold(false, Boolean::or)
    }

    /**
     * Assumes this type is a the same as or a subtype of the given type (see [BaseType.isSubtypeOf] to
     * assure that).
     * Returns how many steps in hierarchy are between this type and the given type.
     *
     * For Example: `B : A`, `C : B`, `D : B`
     *
     * |~.hierarchicalDistanceTo(A)|return value|
     * |---------------------------|------------|
     * |A                          |0           |
     * |B                          |1           |
     * |C                          |2           |
     * |D                          |3           |
     *
     * @param carry Used by recursive invocations of this function. Is added to the hierarchical distance.
     * @return The hierarchical distance
     * @throws IllegalArgumentException If the given type is not a supertype of this type.
     */
    fun hierarchicalDistanceTo(superType: BaseType, carry: Int = 0): Int {
        if (this == superType) return carry

        if (this isSubtypeOf superType) {
            return this.superTypes
                .map { it.hierarchicalDistanceTo(superType, carry + 1) }
                .sorted()
                .first()
        }

        throw IllegalArgumentException("The given type is not a supertype of the receiving type.")
    }

    /** @return The member function overloads for the given name or an empty collection if no such member function is defined. */
    fun resolveMemberFunction(name: String): Collection<FunctionDeclaration> = emptySet()
}