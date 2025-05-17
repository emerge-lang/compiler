package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.ast.type.TypeMutability

class DecoratingMemberVariableWithNonReadTypeDiagnostic(
    memberVariable: BaseTypeMemberVariableDeclaration,
    actualMutability: TypeMutability,
) : Diagnostic(
    Severity.ERROR,
    run {
        val inferredStr = when (memberVariable.variableDeclaration.type) {
            null -> " inferred to be"
            else -> ""
        }
        "Decorated member variables must have a read type, this one is $inferredStr${actualMutability.keyword.text}"
    },
    memberVariable.variableDeclaration.type?.span ?: memberVariable.span,
)