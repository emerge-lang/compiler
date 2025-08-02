package compiler.diagnostic

import compiler.ast.Executable
import compiler.diagnostic.rendering.CellBuilder

class UnreachableCodeDiagnostic(
    val previousCodeThatTerminates: Executable,
    val unreachableCode: Executable,
) : Diagnostic(
    Severity.WARNING,
    "This code is not reachable",
    unreachableCode.span,
) {
    context(CellBuilder)
    override fun renderBody() {
        sourceHints(
            SourceHint(previousCodeThatTerminates.span, "this code always terminates"),
            SourceHint(unreachableCode.span, "so this code will never execute", severity = Severity.WARNING)
        )
    }
}