package compiler.compiler.negative

import compiler.diagnostic.ConditionNotBooleanDiagnostic
import compiler.diagnostic.MutationInConditionDiagnostic
import io.kotest.core.spec.style.FreeSpec

class ConditionErrors : FreeSpec({
    "if" - {
        "if on non-Bool" {
            validateModule("""
                fn test() {
                    if 3 {
                    
                    }
                }
            """.trimIndent())
                .shouldFind<ConditionNotBooleanDiagnostic>()
        }

        "if containing mutation" - {
            "global" {
                validateModule("""
                    intrinsic mut fn modify() -> Bool 
                    fn test() {
                        if modify() {
                            
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "local" {
                validateModule("""
                    class Box {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(p: mut Box) -> Bool
                    fn test() {
                        var localBox = Box()
                        if modify(localBox) {
                            
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }
        }
    }

    "while" - {
        "while on non-bool" {
            validateModule("""
                fn test() {
                    while 3 {
                    }
                }
            """.trimIndent())
                .shouldFind<ConditionNotBooleanDiagnostic>()
        }

        "while containing mutation" - {
            "global" {
                validateModule("""
                    intrinsic mut fn modify() -> Bool 
                    fn test() {
                        while modify() {
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "local" {
                validateModule("""
                    class Box {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(p: mut Box) -> Bool
                    fn test() {
                        var localBox = Box()
                        while modify(localBox) {
                            
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }
        }
    }

    "do-while" - {
        "do-while on non-bool" {
            validateModule("""
                fn test() {
                    do {
                    } while 3
                }
            """.trimIndent())
                .shouldFind<ConditionNotBooleanDiagnostic>()
        }

        "do-while containing mutation" - {
            "global" {
                validateModule("""
                    intrinsic mut fn modify() -> Bool 
                    fn test() {
                        do {
                        } while modify()
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "local" {
                validateModule("""
                    class Box {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(p: mut Box) -> Bool
                    fn test() {
                        var localBox = Box()
                        do {
                            
                        } while modify(localBox)
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }
        }
    }
})