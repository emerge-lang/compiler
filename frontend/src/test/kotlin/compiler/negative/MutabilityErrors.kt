package compiler.compiler.negative

import compiler.diagnostic.ValueNotAssignableDiagnostic
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
                fn test() {
                    myX = X(2)
                    set myX.a = 3
                }
            """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "cannot be assigned to a mut reference" {
            validateModule("""
                class X {
                    a: S32 = init
                }
                fn test() {
                    myX = X(2)
                    var otherX: mut X = myX
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "cannot assign a const value to a mut reference"
                }
        }

        "can be assigned to an const reference" {
            validateModule("""
                class X {
                    a: S32 = init
                }
                fn test() {
                    myX = X(2)
                    otherX: const X = myX
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "mutability from use-site generics" - {
        "prohibits writes to const element" {
            validateModule("""
                class A {
                    someVal: S32 = init
                }
                class B<T> {
                    var genericVal: T = init
                }
                fn test() {
                    myB: mut B<const A> = B::<const A>(A(3))
                    set myB.genericVal = A(2)
                    set myB.genericVal.someVal = 5
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.targetType.toString() shouldBe "mut testmodule.A"
                    it.sourceType.toString() shouldBe "const testmodule.A"
                }
        }
    }

    "mutability errors when calling functions" - {
        "mut value to const parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: const S) {}
                fn test(p: mut S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "A const value is needed here, this one is mut."
                }
        }

        "read value to mut parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: mut S) {}
                fn test(p: read S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "Cannot mutate this value, this is a read reference."
                }
        }

        "read value to const parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: const S) {}
                fn test(p: read S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "A const value is needed here. This is a read reference, immutability is not guaranteed."
                }
        }

        "const value to mut parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: mut S) {}
                fn test(p: const S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "Cannot mutate this value. In fact, this is an const value."
                }
        }

        "mut value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fn foo(p: exclusive S) {}
                fn test(p: mut S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "An exclusive value is needed here, this one is mut."
                }
        }

        "read value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fn foo(p: exclusive S) {}
                fn test(p: read S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "An exclusive value is needed here; this is a read reference."
                }
        }

        "const value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fn foo(p: exclusive S) {}
                fn test(p: const S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "An exclusive value is needed here, this one is const."
                }
        }
    }
})