package compiler.compiler.negative

import compiler.reportings.ConditionNotBooleanDiagnostic
import compiler.reportings.MutationInConditionDiagnostic
import io.kotest.core.spec.style.FreeSpec

class ConditionErrors : FreeSpec({
    "if on non-Bool" {
        validateModule("""
            fn test() {
                if 3 {
                
                }
            }
        """.trimIndent())
            .shouldReport<ConditionNotBooleanDiagnostic>()
    }

    "if containing mutation" {
        validateModule("""
            intrinsic mut fn modify() -> Bool 
            fn test() {
                if modify() {
                    
                }
            }
        """.trimIndent())
            .shouldReport<MutationInConditionDiagnostic>()
    }

    "while on non-bool" {
        validateModule("""
            fn test() {
                while 3 {
                }
            }
        """.trimIndent())
            .shouldReport<ConditionNotBooleanDiagnostic>()
    }

    "while containing mutation" {
        validateModule("""
            intrinsic mut fn modify() -> Bool 
            fn test() {
                while modify() {
                }
            }
        """.trimIndent())
            .shouldReport<MutationInConditionDiagnostic>()
    }
})