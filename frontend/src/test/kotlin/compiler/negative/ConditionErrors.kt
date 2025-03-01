package compiler.compiler.negative

import compiler.diagnostic.ConditionNotBooleanDiagnostic
import compiler.diagnostic.MutationInConditionDiagnostic
import io.kotest.core.spec.style.FreeSpec

class ConditionErrors : FreeSpec({
    "if on non-Bool" {
        validateModule("""
            fn test() {
                if 3 {
                
                }
            }
        """.trimIndent())
            .shouldFind<ConditionNotBooleanDiagnostic>()
    }

    "if containing mutation" {
        validateModule("""
            intrinsic mut fn modify() -> Bool 
            fn test() {
                if modify() {
                    
                }
            }
        """.trimIndent())
            .shouldFind<MutationInConditionDiagnostic>()
    }

    "while on non-bool" {
        validateModule("""
            fn test() {
                while 3 {
                }
            }
        """.trimIndent())
            .shouldFind<ConditionNotBooleanDiagnostic>()
    }

    "while containing mutation" {
        validateModule("""
            intrinsic mut fn modify() -> Bool 
            fn test() {
                while modify() {
                }
            }
        """.trimIndent())
            .shouldFind<MutationInConditionDiagnostic>()
    }
})