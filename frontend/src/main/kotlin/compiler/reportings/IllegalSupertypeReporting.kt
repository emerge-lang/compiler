package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation

class IllegalSupertypeReporting(
    val supertype: TypeReference,
    reason: String,
) : Reporting(
    Level.ERROR,
    "Cannot inherit from this type: $reason",
    supertype.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IllegalSupertypeReporting) return false

        if (supertype.sourceLocation != other.supertype.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.sourceLocation.hashCode()
    }
}