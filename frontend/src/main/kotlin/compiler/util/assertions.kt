package compiler.util

import compiler.reportings.Reporting

internal fun checkNoDiagnostics(reportings: Collection<Reporting>) {
    check(reportings.isEmpty()) {
        reportings.joinToString(
            prefix = "Generated code produced diagnostics!:\n\n",
            separator = "\n\n"
        )
    }
}