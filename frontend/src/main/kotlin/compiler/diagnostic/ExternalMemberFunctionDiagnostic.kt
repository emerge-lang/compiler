package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.lexer.Token

class ExternalMemberFunctionDiagnostic(
    val memberFunction: FunctionDeclaration,
    val externalKeyword: Token,
) : Diagnostic(
    Severity.ERROR,
    "Member functions cannot be external; declare ${memberFunction.name.value} as a top-level function instead.",
    externalKeyword.span,
)