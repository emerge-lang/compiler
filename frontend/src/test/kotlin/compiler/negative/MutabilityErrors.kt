package compiler.compiler.negative

import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class MutabilityErrors : FreeSpec({
    "class initialized in a val is immutable" - {
        "members cannot be mutated" {
            validateModule("""
                class X {
                    var a: S32 = init
                }
                fun test() {
                    myX = X(2)
                    set myX.a = 3
                }
            """.trimIndent())
                    .shouldReport<ValueNotAssignableReporting>()
        }

        "cannot be assigned to a mutable reference" {
            validateModule("""
                class X {
                    a: S32 = init
                }
                fun test() {
                    myX = X(2)
                    var otherX: mutable X = myX
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.reason shouldBe "cannot assign a immutable value to a mutable reference"
                }
        }

        "can be assigned to an immutable reference" {
            validateModule("""
                class X {
                    a: S32 = init
                }
                fun test() {
                    myX = X(2)
                    otherX: immutable X = myX
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "mutability from use-site generics" - {
        "prohibits writes to immutable element" {
            validateModule("""
                class A {
                    someVal: S32 = init
                }
                class B<T> {
                    genericVal: T = init
                }
                fun test() {
                    myB: mutable B<immutable A> = B::<immutable A>(A(3))
                    set myB.genericVal = A(2)
                    set myB.genericVal.someVal = 5
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.targetType.toString() shouldBe "mutable testmodule.A"
                    it.sourceType.toString() shouldBe "immutable testmodule.A"
                }
        }
    }

    "mutability errors when calling functions" - {
        "mutable value to immutable parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fun foo(p: immutable S) {}
                fun test(p: mutable S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "An immutable value is needed here, this one is mutable."
                }
        }

        "readonly value to mutable parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fun foo(p: mutable S) {}
                fun test(p: readonly S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "Cannot mutate this value, this is a readonly reference."
                }
        }

        "readonly value to immutable parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fun foo(p: immutable S) {}
                fun test(p: readonly S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "An immutable value is needed here. This is a readonly reference, immutability is not guaranteed."
                }
        }

        "immutable value to mutable parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fun foo(p: mutable S) {}
                fun test(p: immutable S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "Cannot mutate this value. In fact, this is an immutable value."
                }
        }

        "mutable value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fun foo(p: exclusive S) {}
                fun test(p: mutable S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "An exclusive value is needed here, this one is mutable."
                }
        }

        "readonly value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fun foo(p: exclusive S) {}
                fun test(p: readonly S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "An exclusive value is needed here; this is a readonly reference."
                }
        }

        "immutable value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fun foo(p: exclusive S) {}
                fun test(p: immutable S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "An exclusive value is needed here, this one is immutable."
                }
        }
    }
})