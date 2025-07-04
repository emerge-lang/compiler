package compiler.compiler.negative

import compiler.diagnostic.BreakOutsideOfLoopDiagnostic
import compiler.diagnostic.ContinueOutsideOfLoopDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class LoopErrors : FreeSpec({
    "break outside of loop" {
        validateModule("""
            fn test() {
                break
            }
        """.trimIndent())
            .shouldFind<BreakOutsideOfLoopDiagnostic>()
    }

    "continue outside of loop" {
        validateModule("""
            fn test() {
                continue
            }
        """.trimIndent())
            .shouldFind<ContinueOutsideOfLoopDiagnostic>()
    }

    "foreach" - {
        "not an iterable" {
            validateModule("""
                class NotAnIterable {}
                
                fn test() -> Any {
                    foreach e in NotAnIterable() {
                        return e
                    }
                    
                    return 0
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "exclusive testmodule.NotAnIterable"
                    it.targetType.toString() shouldBe "read emerge.core.range.Iterable<out read Any>"
                }
        }
    }
})