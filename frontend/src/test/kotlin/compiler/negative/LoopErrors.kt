package compiler.compiler.negative

import compiler.reportings.BreakOutsideOfLoopReporting
import compiler.reportings.ContinueOutsideOfLoopReporting
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

    "continue outside of loop" {
        validateModule("""
            fn test() {
                continue
            }
        """.trimIndent())
            .shouldReport<ContinueOutsideOfLoopReporting>()
    }
})