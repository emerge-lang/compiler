package compiler.reportings

import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken

class UnresolvableConstructorReporting(
    val typeName: IdentifierToken,
    val parameterTypes: List<BaseTypeReference?>,
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
    typeName.sourceLocation,
)