package compiler.diagnostic

import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.binding.BoundMemberFunction
import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Keyword

class AbstractInheritedFunctionNotImplementedDiagnostic(
    val implementingType: BoundBaseType,
    val functionToImplement: BoundMemberFunction,
) : Diagnostic(
    Severity.ERROR,
    """
        Class ${implementingType.simpleName} must implement abstract function ${functionToImplement.name} inherited from ${functionToImplement.declaredOnType.canonicalName}. Implement this member function:
        ${functionToImplement.synopsis}
    """.trimIndent(),
    implementingType.declaration.declaredAt,
) {
    override fun equals(other: Any?): Boolean {
        if (other == null) return false
        if (other === this) return true

        if (other !is AbstractInheritedFunctionNotImplementedDiagnostic) return false

        if (other.span != this.span) return false
        if (other.functionToImplement !== this.functionToImplement) return false

        return true
    }

    override fun hashCode(): Int {
        var result = span.hashCode()
        result = 31 * result + System.identityHashCode(functionToImplement)
        return result
    }
}

private val BoundMemberFunction.synopsis: String get() {
    var signature = ""
    if (this.declaredTypeParameters.isNotEmpty()) {
        signature += this.declaredTypeParameters.joinToString(
            prefix = "<",
            separator = ", ",
            postfix = ">",
        )
    }
    signature += "("
    var parameterTypesForSignature = this.parameterTypes
    if (this.declaresReceiver) {
        val selfParam = this.parameters.declaredReceiver!!
        if (selfParam.ownershipAtDeclarationTime != VariableOwnership.BORROWED) {
            signature += selfParam.ownershipAtDeclarationTime.name.lowercase()
            signature += " "
        }
        signature += "self"
        val mutability = selfParam.typeAtDeclarationTime?.mutability
        if (mutability != null && mutability != TypeMutability.READONLY) {
            signature += ": "
            signature += mutability.keyword.text
            signature += " _"
        }
        parameterTypesForSignature = parameterTypesForSignature.drop(1)
        if (parameterTypesForSignature.isNotEmpty()) {
            signature += ", "
        }
    }
    signature += parameterTypesForSignature.joinToString(separator = ", ")
    signature += ") -> "
    signature += this.returnType.toString()

    // the nothrow attribute is the only one that is contagious/is forced on overriding functions;
    // the others are mostly optional or not straightforward. This keeps things simple while still sufficiently informative
    val nothrowText = if (this.attributes.isDeclaredNothrow) Keyword.NOTHROW.text + " " else ""

    return "${nothrowText}${Keyword.FUNCTION.text} ${name}$signature"
}