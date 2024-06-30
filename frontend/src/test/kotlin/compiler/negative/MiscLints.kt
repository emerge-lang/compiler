package compiler.compiler.negative

import compiler.reportings.NullCheckingNonNullableValueReporting
import io.kotest.core.spec.style.FreeSpec

class MiscLints : FreeSpec({
    "null-coalesce on non-nullable value is reported" {
        validateModule("""
            fn test(p: String) -> String {
                return p ?: "default"
            }
        """.trimIndent())
            .shouldReport<NullCheckingNonNullableValueReporting>()
    }
})