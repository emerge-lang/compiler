package compiler.reportings

import compiler.binding.type.BoundTypeReference
import compiler.lexer.IdentifierToken

class UnresolvableConstructorReporting(
    val typeName: IdentifierToken,
    val parameterTypes: List<BoundTypeReference?>,
    val functionsWithSameNameAvailable: Boolean,
) : Reporting(
    Level.ERROR,
    run {
        var message = "Type ${typeName.value} does not have a constructor for types ${parameterTypes.typeTupleToString()}."
        if (functionsWithSameNameAvailable) {
            message += " Function ${typeName.value} and its overloads was not considered for this invocation."
        }
        message
    },
    typeName.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is UnresolvableConstructorReporting) return false

        if (typeName != other.typeName) return false

        return true
    }

    override fun hashCode(): Int {
        return typeName.hashCode()
    }
}