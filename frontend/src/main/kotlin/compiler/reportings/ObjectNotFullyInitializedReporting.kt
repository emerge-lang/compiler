package compiler.reportings

import compiler.ast.ClassMemberVariableDeclaration
import compiler.binding.type.BaseType
import compiler.lexer.SourceLocation

class ObjectNotFullyInitializedReporting(
    val baseType: BaseType,
    val uninitializedMembers: Collection<ClassMemberVariableDeclaration>,
    sourceLocation: SourceLocation,
) : Reporting(
    Level.ERROR,
    run {
        val memberList = uninitializedMembers.joinToString(transform = { "- ${it.name.value}" }, separator = "\n")
        "The object is not fully initialized at this point, it cannot be used regularly yet. These member variables must still be initialized:\n$memberList"
    },
    sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ObjectNotFullyInitializedReporting) return false

        if (sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        return sourceLocation.hashCode()
    }
}