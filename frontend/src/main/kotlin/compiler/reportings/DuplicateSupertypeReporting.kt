package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation

class DuplicateSupertypeReporting(
    val supertype: TypeReference,
) : Reporting(
    Level.ERROR,
    "Can inherit from ${supertype.simpleName} only once",
    supertype.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DuplicateSupertypeReporting) return false

        if (supertype.sourceLocation != other.supertype.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.sourceLocation.hashCode()
    }
}