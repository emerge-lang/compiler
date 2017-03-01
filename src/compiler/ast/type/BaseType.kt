package compiler.ast.type

import compiler.ast.FunctionDeclaration

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

    val defaultReference: TypeReference
        get() = TypeReference(fullyQualifiedName, false, impliedModifier)

    val superTypes: Set<BaseType>
        get() = emptySet()

    /** @return The member function overloads for the given name or an empty collection if no such member function is defined. */
    fun resolveMemberFunction(name: String): Collection<FunctionDeclaration>
}