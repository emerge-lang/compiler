package compiler.reportings

import compiler.binding.BoundMemberFunction
import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Keyword

class AbstractInheritedFunctionNotImplementedReporting(
    val implementingType: BoundBaseType,
    val functionToImplement: BoundMemberFunction,
) : Reporting(
    Level.ERROR,
    run {
        var signature = ""
        if (functionToImplement.declaredTypeParameters.isNotEmpty()) {
            signature += functionToImplement.declaredTypeParameters.joinToString(
                prefix = "<",
                separator = ", ",
                postfix = ">",
            )
        }
        signature += "("
        var parameterTypesForSignature = functionToImplement.parameterTypes
        if (functionToImplement.declaresReceiver) {
            signature += "self"
            parameterTypesForSignature = parameterTypesForSignature.drop(1)
            if (parameterTypesForSignature.isNotEmpty()) {
                signature += ", "
            }
        }
        signature += parameterTypesForSignature.joinToString(separator = ", ")
        signature += ") -> "
        signature += functionToImplement.returnType.toString()

        """
            Class ${implementingType.simpleName} must implement abstract function ${functionToImplement.name} inherited from ${functionToImplement.declaredOnType.canonicalName}. Implement this member function:
            ${Keyword.FUNCTION.text} ${functionToImplement.name}$signature
        """.trimIndent()
    },
    implementingType.declaration.declaredAt,
) {
    override fun equals(other: Any?): Boolean {
        if (other == null) return false
        if (other === this) return true

        if (other !is AbstractInheritedFunctionNotImplementedReporting) return false

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