package compiler.diagnostic

import compiler.ast.BaseTypeDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable

/**
 * A type says itself whether its instances are tokens: where it is a subtype of a token type, and where it
 * holds what may be a token.
 */
class MissingTokenModifierDiagnostic(
    val baseType: BaseTypeDeclaration,
    val reason: Reason,
) : Diagnostic(
    Severity.ERROR,
    "${baseType.declarationKeyword.keyword.text} ${baseType.name.value} ${reason.description}",
    baseType.declaredAt,
) {
    sealed interface Reason {
        val description: String

        class Supertype(val supertype: BoundBaseType) : Reason {
            override val description = "must be declared token: its supertype ${supertype.simpleName} is a token type"
        }

        class MemberVariable(val memberVariable: BoundBaseTypeMemberVariable) : Reason {
            override val description = "must be declared token, or inherit from NonToken: the type of its member variable ${memberVariable.name.quoteIdentifier()} may be a token. With NonToken, the member variable only takes values that are no tokens."
        }
    }
}
