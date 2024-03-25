package compiler.compiler.negative

import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.reportings.IllegalAssignmentReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class MutabilityErrors : FreeSpec({
    "class initialized in a val is immutable" - {
        "members cannot be mutated" {
            validateModule("""
                class X {
                    var a: Int = init
                }
                fun test() {
                    myX = X(2)
                    set myX.a = 3
                }
            """.trimIndent())
                    .shouldReport<IllegalAssignmentReporting> {
                        it.statement.targetExpression.shouldBeInstanceOf<BoundMemberAccessExpression>().let { targetExpr ->
                            targetExpr.valueExpression.shouldBeInstanceOf<BoundIdentifierExpression>().identifier shouldBe "myX"
                            targetExpr.memberName shouldBe "a"
                        }
                    }
        }

        "cannot be assigned to a mutable reference" {
            validateModule("""
                class X {
                    a: Int = init
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
                    a: Int = init
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
                    someVal: Int = init
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
                .shouldReport<IllegalAssignmentReporting> {
                    it.statement.targetExpression.shouldBeInstanceOf<BoundMemberAccessExpression>().memberName shouldBe "someVal"
                }
        }
    }

    "mutability errors when calling functions" - {
        "mutable value to immutable parameter" {
            validateModule("""
                class S {
                    field: Int
                }
                fun foo(p: immutable S) {}
                fun test(p: mutable S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.message shouldBe "An immutable value is needed here, this one is immutable."
                }
        }

        "readonly value to mutable parameter" {
            validateModule("""
                class S {
                    field: Int
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
                    field: Int
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
                    field: Int
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
    }
})