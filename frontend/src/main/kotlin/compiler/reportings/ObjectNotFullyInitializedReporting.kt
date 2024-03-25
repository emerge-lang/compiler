package compiler.reportings

import compiler.ast.ClassMemberVariableDeclaration
import compiler.lexer.SourceLocation

class ObjectNotFullyInitializedReporting(
    val uninitializedMembers: Collection<ClassMemberVariableDeclaration>,
    sourceLocation: SourceLocation,
) : Reporting(
    Level.ERROR,
    run {
        val memberList = uninitializedMembers.joinToString(transform = { "- ${it.name.value}" }, separator = "\n")
        "The object is not fully initialized yet. These member variables must be initialized before the object can be used regularly:\n$memberList"
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