package compiler.negative

import compiler.reportings.AssignmentInConditionReporting
import compiler.reportings.ConditionNotBooleanReporting
import compiler.reportings.MutationInConditionReporting
import io.kotest.core.spec.style.FreeSpec

class ConditionErrors : FreeSpec({
    "if on non-boolean" {
        validateModule("""
            fun test() {
                if 3 {
                
                }
            }
        """.trimIndent())
            .shouldReport<ConditionNotBooleanReporting>()
    }

    "if containing assignment" {
        validateModule("""
            fun test() {
                var x = false
                if x = true {
                    
                }
            }
        """.trimIndent())
            .shouldReport<AssignmentInConditionReporting>()
    }

    "if containing mutation" {
        validateModule("""
            var x = 0
            fun modifyingFn() -> Boolean {
                x = 1
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