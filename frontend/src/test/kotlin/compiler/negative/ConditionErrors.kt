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
            intrinsic mut fn modify() -> Bool 
            fn test() {
                if modify() {
                    
                }
            }
        """.trimIndent())
            .shouldReport<MutationInConditionReporting>()
    }

    "while on non-bool" {
        validateModule("""
            fn test() {
                while 3 {
                }
            }
        """.trimIndent())
            .shouldReport<ConditionNotBooleanReporting>()
    }

    "while containing mutation" {
        validateModule("""
            intrinsic mut fn modify() -> Bool 
            fn test() {
                while modify() {
                }
            }
        """.trimIndent())
            .shouldReport<MutationInConditionReporting>()
    }
})