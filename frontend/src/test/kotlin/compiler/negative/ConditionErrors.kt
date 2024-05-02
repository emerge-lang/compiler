package compiler.compiler.negative

import compiler.reportings.ConditionNotBooleanReporting
import compiler.reportings.MutationInConditionReporting
import io.kotest.core.spec.style.FreeSpec

class ConditionErrors : FreeSpec({
    "if on non-Bool" {
        validateModule("""
            fn test() {
                if 3 {
                
                }
            }
        """.trimIndent())
            .shouldReport<ConditionNotBooleanReporting>()
    }

    "if containing mutation" {
        validateModule("""
            var x = 0
            mut fn modifyingFn() -> Bool {
                set x = 1
                return true
            }
            fn test() {
                if modifyingFn() {
                    
                }
            }
        """.trimIndent())
            .shouldReport<MutationInConditionReporting>()
    }
})