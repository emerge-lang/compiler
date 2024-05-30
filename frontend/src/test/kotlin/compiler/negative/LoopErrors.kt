package compiler.compiler.negative

import compiler.reportings.BreakOutsideOfLoopReporting
import io.kotest.core.spec.style.FreeSpec

class LoopErrors : FreeSpec({
    "break outside of loop" {
        validateModule("""
            fn test() {
                break
            }
        """.trimIndent())
            .shouldReport<BreakOutsideOfLoopReporting>()
    }
})