package compiler.util

import compiler.diagnostic.Diagnostic

internal fun checkNoDiagnostics(diagnostics: Collection<Diagnostic>) {
    check(diagnostics.isEmpty()) {
        diagnostics.joinToString(
            prefix = "Generated code produced diagnostics!:\n\n",
            separator = "\n\n"
        )
    }
}