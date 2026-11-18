package compiler.binding.type

import compiler.binding.basetype.BoundBaseType

/**
 * What the compiler knows about the classes of the values of a type at runtime, see [BoundTypeReference.possibleRuntimeTypes].
 */
sealed interface PossibleRuntimeTypes {
    /**
     * Every value is an instance of one of [classes], or `null` if [includesNull]. The compiler sees the declarations
     * of all the subtypes, e.g. because the type is an interface that is private to its module.
     */
    data class Closed(val classes: Set<BoundBaseType>, val includesNull: Boolean) : PossibleRuntimeTypes

    /**
     * Code the compiler doesn't see can declare more subtypes.
     * @param reason why that is so, to be used in diagnostics. A full sentence, e.g. "`Foo` is exported, so other modules can declare subtypes"
     */
    data class Open(val reason: String) : PossibleRuntimeTypes
}
