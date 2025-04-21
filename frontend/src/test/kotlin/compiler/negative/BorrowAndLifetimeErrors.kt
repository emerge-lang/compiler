package compiler.compiler.negative

import compiler.diagnostic.BorrowedVariableCapturedDiagnostic
import compiler.diagnostic.ExtendingOwnershipOverrideDiagnostic
import compiler.diagnostic.LifetimeEndingCaptureInLoopDiagnostic
import compiler.diagnostic.SimultaneousIncompatibleBorrowsDiagnostic
import compiler.diagnostic.VariableUsedAfterLifetimeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BorrowAndLifetimeErrors : FreeSpec({
    "initializing a variable ends the lifetime" - {
        "use by reading a raw member" {
            validateModule("""
                class Test {
                    m: S32 = 0
                }
                fn test() -> S32 {
                    v: exclusive _ = Test()
                    v2 = v
                    return v.m
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }

        "use by reading a virtual member" {
            validateModule("""
                class Test {
                    get fn m(self) -> S32
                }
                fn test() -> S32 {
                    v: exclusive _ = Test()
                    v2 = v
                    return v.m
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }

        "use by writing a raw member" {
            validateModule("""
                class Test {
                    var m: S32 = 0
                }
                fn test() {
                    v: exclusive _ = Test()
                    v2 = v
                    set v.m = 1
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }

        "use by writing a virtual member" {
            validateModule("""
                class Test {
                    set fn m(self: mut _, v: S32)
                }
                fn test() {
                    v: exclusive _ = Test()
                    v2 = v
                    set v.m = 1
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }

        "use by return" {
            validateModule("""
                class Test {}
                fn test() -> const Test {
                    v: exclusive _ = Test()
                    v2 = v
                    return v
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }
    }

    "assigning to a variable ends the lifetime" {
        validateModule("""
            class Test {}
            fn test() -> Test {
                var v2: const _ = Test()
                v: exclusive _ = Test()
                set v2 = v
                return v
            }
        """.trimIndent())
            .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                it.variable.name.value shouldBe "v"
                it.lifetimeEndedMaybe shouldBe false
            }
    }

    "passing to capturing function parameter ends lifetime" {
        validateModule("""
            class Test {}
            fn test() -> Test {
                v: exclusive _ = Test()
                captureValue(v)
                return v
            }
            fn captureValue(p: const Test) {}
        """.trimIndent())
            .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                it.variable.name.value shouldBe "v"
                it.lifetimeEndedMaybe shouldBe false
            }
    }

    "branching" - {
        "lifetime ended in then-only if" {
            validateModule("""
                class Test {}
                fn captureValue(p: Test) {}
                fn test(cond: Bool) {
                    v: exclusive _ = Test()
                    if (cond) {
                        v2 = v
                    }
                    captureValue(v)
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe true
                }
        }

        "lifetime ended in one branch of if" {
            validateModule("""
                class Test {}
                fn captureValue(p: Test) {}
                fn test(cond: Bool) {
                    v: exclusive _ = Test()
                    if (cond) {
                        v2 = v
                    } else {
                    }
                    captureValue(v)
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe true
                }
        }

        "lifetime ended in both branches of if" {
            validateModule("""
                class Test {}
                fn captureValue(p: Test) {}
                fn test(cond: Bool) {
                    v: exclusive _ = Test()
                    if (cond) {
                        v2 = v
                    } else {
                        v3 = v
                    }
                    captureValue(v)
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "v"
                    it.lifetimeEndedMaybe shouldBe false
                }
        }
    }

    "loops" - {
        "capturing exclusive in while loop" {
            validateModule("""
                class C {}
                fn test(p: exclusive C) {
                    while true {
                        captureValue(p)
                    }
                }
                intrinsic fn captureValue(p: const Any)
            """.trimIndent())
                .shouldFind<LifetimeEndingCaptureInLoopDiagnostic>()
        }
    }

    "borrowed variable cannot be captured" - {
        "capture by passing to a capturing function parameter" {
            validateModule("""
                class Test {}
                fn captureValue(p1: Test) {}
                fn test(borrow p2: Test) {
                    captureValue(p2)
                }
            """.trimIndent())
                .shouldFind<BorrowedVariableCapturedDiagnostic> {
                    it.variable.name.value shouldBe "p2"
                }

            validateModule("""
                class Dummy {}
                class Test {
                    fn captureValue(self, p1: Dummy) {}
                    fn test(self, borrow p2: Dummy) {
                        self.captureValue(p2)
                    }
                }
            """.trimIndent())
                .shouldFind<BorrowedVariableCapturedDiagnostic> {
                    it.variable.name.value shouldBe "p2"
                }
        }

        "capture by initializing a variable" {
            validateModule("""
                class Test {}
                fn test(borrow p2: Test) {
                    p3 = p2
                }
            """.trimIndent())
                .shouldFind<BorrowedVariableCapturedDiagnostic> {
                    it.variable.name.value shouldBe "p2"
                }
        }

        "capture by passing assigning to a variable" {
            validateModule("""
                class Test {}
                fn test(borrow p2: Test) {
                    var v = Test()
                    v = p2
                }
            """.trimIndent())
                .shouldFind<BorrowedVariableCapturedDiagnostic> {
                    it.variable.name.value shouldBe "p2"
                }
        }
    }

    "exclusive value can be borrowed both mutably and immutably" {
        validateModule("""
            class Test {
                m: S32 = 0
            }
            fn borrowMut(borrow p1: mut Test) {}
            fn borrowImm(borrow p2: const Test) {}
            fn test() -> Test {
                v: exclusive _ = Test()
                borrowMut(v)
                borrowImm(v)
                return v
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "read capture doesn't end a lifetime" {
        validateModule("""
            class Test {
                m: S32 = 0
            }
            fn captureRead(p1: read Test) {}
            fn test() -> Test {
                v: exclusive _ = Test()
                captureRead(v)
                return v
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "reassigning a variable resets the lifetime" - {
        "definitely with linear control flow" {
            validateModule("""
                class Test {}
                fn captureValue(p: const Any) {}
                fn test() {
                    var v1: exclusive _ = Test()
                    captureValue(v1)
                    set v1 = Test()
                    captureValue(v1)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "definitely with branched control flow" {
            validateModule("""
                class Test {}
                fn captureValue(p: const Any) {}
                fn test(cond: Bool) {
                    var v1: exclusive _ = Test()
                    captureValue(v1)
                    if cond {
                        set v1 = Test()
                    } else {
                        set v1 = Test()
                    }
                    captureValue(v1)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "maybe with branched control flow" {
            validateModule("""
                class Test {}
                fn captureValue(p: const Any) {}
                fn test(cond: Bool) {
                    var v1: exclusive _ = Test()
                    captureValue(v1)
                    if cond {
                        set v1 = Test()
                    }
                    captureValue(v1)
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic>()
        }
    }

    "borrowing X overriding" - {
        "overriding function cannot capture a parameter that's borrowed in the parent function" {
            validateModule("""
                interface I {
                    fn foo(self, borrow p: String)
                }
                class C : I {
                    override fn foo(self, capture p: String) {}
                } 
            """.trimIndent())
                .shouldFind<ExtendingOwnershipOverrideDiagnostic>()
        }

        "overriding function can borrow a parameter that's captured in the parent function" {
            validateModule("""
                interface I {
                    fn foo(self, capture p: String)
                }
                class C : I {
                    override fn foo(self, borrow p: String) {}
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "simultaneous borrows" - {
        "first read borrow, then mut borrow - OK" {
            validateModule("""
                class C {}
                fn test() {
                    c: exclusive _ = C()
                    trigger(c, c)
                }
                fn trigger(borrow a: read C, borrow b: mut C) {}
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "first mut borrow, then read borrow - OK" {
            validateModule("""
                class C {}
                fn test() {
                    c: exclusive _ = C()
                    trigger(c, c)
                }
                fn trigger(borrow a: mut C, borrow b: read C) {}
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "first mut borrow, then mut borrow - OK" {
            validateModule("""
                class C {}
                fn test() {
                    c: exclusive _ = C()
                    trigger(c, c)
                }
                fn trigger(borrow a: mut C, borrow b: mut C) {}
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "first const borrow, then mut borrow - ERROR" {
            validateModule("""
                class C {}
                fn test() {
                    c: exclusive _ = C()
                    trigger(c, c)
                }
                fn trigger(borrow a: const C, borrow b: mut C) {}
            """.trimIndent())
                .shouldFind<SimultaneousIncompatibleBorrowsDiagnostic>()
        }

        "first mut borrow, then const borrow - ERROR" {
            validateModule("""
                class C {}
                fn test() {
                    c: exclusive _ = C()
                    trigger(c, c)
                }
                fn trigger(borrow a: mut C, borrow b: const C) {}
            """.trimIndent())
                .shouldFind<SimultaneousIncompatibleBorrowsDiagnostic>()
        }

        "start and complete a const borrow, then start and complete a mut borrow - OK" {
            validateModule("""
                class C {}
                fn test() {
                    c: exclusive _ = C()
                    borrowConst(c)
                    borrowMut(c)
                }
                fn borrowMut(borrow p: mut C) {}
                fn borrowConst(borrow p: const C) {}
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "re-borrowing an exclusive borrow incompatibly" {
            validateModule("""
                class C {}
                fn test(borrow p: exclusive C) {
                    trigger(p, p)
                }
                fn trigger(borrow a: mut C, borrow b: const C) {}
            """.trimIndent())
                .shouldFind<SimultaneousIncompatibleBorrowsDiagnostic>()
        }
    }
})