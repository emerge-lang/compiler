package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration

class ExplicitMutabilityOnOwnedMemberVariableDiagnostic(
    val memberVariable: BaseTypeMemberVariableDeclaration
) : Diagnostic(
    Severity.ERROR,
    "Member variables cannot explicitly declare mutability because the mutability is always inferred from the reference to the parent object.",
    memberVariable.variableDeclaration.type?.span ?: memberVariable.span, // TODO: get span of mutability keyword
)