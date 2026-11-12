package compiler.diagnostic

import compiler.ast.BaseTypeDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable

/**
 * A type that holds a token, or is a subtype of a token type, has to say so itself.
 */
class MissingTokenModifierDiagnostic(
    val baseType: BaseTypeDeclaration,
    val reason: Reason,
) : Diagnostic(
    Severity.ERROR,
    "${baseType.declarationKeyword.keyword.text} ${baseType.name.value} must be declared token: ${reason.description}",
    baseType.declaredAt,
) {
    sealed interface Reason {
        val description: String

        class Supertype(val supertype: BoundBaseType) : Reason {
            override val description = "its supertype ${supertype.simpleName} is a token type"
        }

        class MemberVariable(val memberVariable: BoundBaseTypeMemberVariable) : Reason {
            override val description = "the type of its member variable ${memberVariable.name.quoteIdentifier()} mentions a token type"
        }
    }
}
