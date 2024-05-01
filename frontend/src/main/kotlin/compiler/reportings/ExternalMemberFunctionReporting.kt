package compiler.reportings

import compiler.ast.FunctionDeclaration
import compiler.lexer.Token

class ExternalMemberFunctionReporting(
    val memberFunction: FunctionDeclaration,
    val externalKeyword: Token,
) : Reporting(
    Level.ERROR,
    "Member functions cannot be external; declare ${memberFunction.name.value} as a top-level function instead.",
    externalKeyword.span,
)