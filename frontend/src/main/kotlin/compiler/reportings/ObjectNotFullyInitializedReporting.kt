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
        "The object is not fully initialized. These members are not initialized yet:\n$memberList"
    },
    sourceLocation,
)