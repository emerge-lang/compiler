package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.lexer.Span

class AccessorContractViolationDiagnostic(
    val accessor: FunctionDeclaration,
    message: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    message,
    span,
)