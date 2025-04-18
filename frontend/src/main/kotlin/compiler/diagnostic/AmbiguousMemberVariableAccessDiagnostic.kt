package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.ast.FunctionDeclaration
import compiler.lexer.Span

class AmbiguousMemberVariableAccessDiagnostic(
    val memberVariableName: String,
    val actualMemberVariable: BaseTypeMemberVariableDeclaration?,
    val possibleAccessors: List<FunctionDeclaration>,
    referenceAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "This reference to member variable `${memberVariableName}` is ambiguous.",
    referenceAt,
)