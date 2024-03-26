package compiler.reportings

import compiler.binding.classdef.BoundClassConstructor
import compiler.lexer.Token

class ConstructorDeclaredModifyingReporting(
    val constructor: BoundClassConstructor,
    val modifyingKeyword: Token,
) : Reporting(
    Level.ERROR,
    "Constructors my not modify global state",
    modifyingKeyword.sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ConstructorDeclaredModifyingReporting) return false

        if (constructor !== other.constructor) return false
        if (modifyingKeyword.sourceLocation != other.modifyingKeyword.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        var result = System.identityHashCode(constructor)
        result = 31 * result + modifyingKeyword.sourceLocation.hashCode()
        return result
    }
}