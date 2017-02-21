package compiler.ast.type

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
}