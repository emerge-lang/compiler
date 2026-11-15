package compiler.compiler.negative

import compiler.diagnostic.ConditionNotBooleanDiagnostic
import compiler.diagnostic.MissingElseBranchDiagnostic
import compiler.diagnostic.MutationInConditionDiagnostic
import compiler.lexer.Keyword
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

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

        "if without else" - {
            "as a value" {
                validateModule("""
                    fn test(p: Bool) -> S32 {
                        x: S32 = if p 1
                        return x
                    }
                """.trimIndent())
                    .shouldFind<MissingElseBranchDiagnostic> {
                        it.keyword.keyword shouldBe Keyword.IF
                    }
            }

            "as a value of inferred type" {
                validateModule("""
                    fn test(p: Bool) {
                        x = if p {
                            1
                        }
                    }
                """.trimIndent())
                    .shouldFind<MissingElseBranchDiagnostic>()
            }

            "as a value in an else-if chain" {
                validateModule("""
                    fn test(p: Bool, q: Bool) -> S32 = if p 1 else if q 2
                """.trimIndent())
                    .shouldFind<MissingElseBranchDiagnostic>()
            }

            "as a Unit value" {
                validateModule("""
                    intrinsic fn sideEffect()
                    fn test(p: Bool) = if p sideEffect()
                    fn test2(p: Bool) {
                        x: Unit = if p sideEffect()
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "as a statement" {
                validateModule("""
                    intrinsic fn compute() -> S32
                    fn test(p: Bool) -> S32 {
                        if p compute()
                        if p {
                            return 1
                        }
                        return 0
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }
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