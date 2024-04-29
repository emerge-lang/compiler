package compiler.compiler.negative

import compiler.reportings.ConditionNotBooleanReporting
import compiler.reportings.MutationInConditionReporting
import io.kotest.core.spec.style.FreeSpec

class ConditionErrors : FreeSpec({
    "if on non-Bool" {
        validateModule("""
            fun test() {
                if 3 {
                
                }
            }
        """.trimIndent())
            .shouldReport<ConditionNotBooleanReporting>()
    }

    "if containing mutation" {
        validateModule("""
            var x = 0
            mutable fun modifyingFn() -> Bool {
                set x = 1
                return true
            }
            fun test() {
                if modifyingFn() {
                    
                }
            }
        """.trimIndent())
            .shouldReport<MutationInConditionReporting>()
    }
})