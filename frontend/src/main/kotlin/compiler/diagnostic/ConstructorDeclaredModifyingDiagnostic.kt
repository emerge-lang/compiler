package compiler.diagnostic

import compiler.binding.basetype.BoundClassConstructor
import compiler.lexer.Token

class ConstructorDeclaredModifyingDiagnostic(
    val constructor: BoundClassConstructor,
    val modifyingKeyword: Token,
) : Diagnostic(
    Severity.ERROR,
    "Constructors my not modify global state",
    modifyingKeyword.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ConstructorDeclaredModifyingDiagnostic) return false

        if (constructor !== other.constructor) return false
        if (modifyingKeyword.span != other.modifyingKeyword.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = System.identityHashCode(constructor)
        result = 31 * result + modifyingKeyword.span.hashCode()
        return result
    }
}