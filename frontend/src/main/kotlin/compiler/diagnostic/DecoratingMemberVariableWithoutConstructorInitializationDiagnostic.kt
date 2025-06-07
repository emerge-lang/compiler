package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.KeywordToken

class DecoratingMemberVariableWithoutConstructorInitializationDiagnostic(
    val memberVariable: BaseTypeMemberVariableDeclaration,
    decoratesAttribute: KeywordToken,
) : Diagnostic(
    Severity.ERROR,
    "Decoration is only meaningful on constructor-initialized member variables.",
    decoratesAttribute.span,
)