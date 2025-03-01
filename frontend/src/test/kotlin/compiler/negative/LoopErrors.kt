package compiler.compiler.negative

import compiler.diagnostic.BreakOutsideOfLoopDiagnostic
import compiler.diagnostic.ContinueOutsideOfLoopDiagnostic
import io.kotest.core.spec.style.FreeSpec

class LoopErrors : FreeSpec({
    "break outside of loop" {
        validateModule("""
            fn test() {
                break
            }
        """.trimIndent())
            .shouldReport<BreakOutsideOfLoopDiagnostic>()
    }

    "continue outside of loop" {
        validateModule("""
            fn test() {
                continue
            }
        """.trimIndent())
            .shouldReport<ContinueOutsideOfLoopDiagnostic>()
    }
})