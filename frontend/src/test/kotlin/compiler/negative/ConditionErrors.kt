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
            "token used as mut" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    fn test(borrow counter: mut Counter) {
                        if modify(counter) {
                            
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "token reached through a field, used as mut" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    token class Holder {
                        counter: mut Counter = init
                    }
                    fn test(borrow holder: mut Holder) {
                        if modify(holder.counter) {
                            
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "token used as read" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn check(borrow c: read Counter) -> Bool
                    fn test(borrow counter: mut Counter) {
                        if check(counter) {
                            
                        }
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "token created inside the condition" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    fn test() {
                        if modify(Counter()) {
                            
                        }
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
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
            "token used as mut" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    fn test(borrow counter: mut Counter) {
                        while modify(counter) {
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "token reached through a field, used as mut" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    token class Holder {
                        counter: mut Counter = init
                    }
                    fn test(borrow holder: mut Holder) {
                        while modify(holder.counter) {
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "token used as read" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn check(borrow c: read Counter) -> Bool
                    fn test(borrow counter: mut Counter) {
                        while check(counter) {
                        }
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "token created inside the condition" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    fn test() {
                        while modify(Counter()) {
                        }
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
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
            "token used as mut" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    fn test(borrow counter: mut Counter) {
                        do {
                        } while modify(counter)
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "token reached through a field, used as mut" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    token class Holder {
                        counter: mut Counter = init
                    }
                    fn test(borrow holder: mut Holder) {
                        do {
                        } while modify(holder.counter)
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
            }

            "token used as read" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn check(borrow c: read Counter) -> Bool
                    fn test(borrow counter: mut Counter) {
                        do {
                        } while check(counter)
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "token created inside the condition" {
                validateModule("""
                    token class Counter {
                        var n: S32 = 0
                    }
                    intrinsic fn modify(borrow c: mut Counter) -> Bool
                    fn test() {
                        do {
                        } while modify(Counter())
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
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