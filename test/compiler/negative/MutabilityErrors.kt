package compiler.compiler.negative

import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.negative.shouldReport
import compiler.negative.validateModule
import compiler.reportings.IllegalAssignmentReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.beEmpty
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class MutabilityErrors : FreeSpec({
    "struct initialized in a val is immutable" - {
        "members cannot be mutated" {
            validateModule("""
                struct X {
                    a: Int
                }
                fun test() {
                    val myX = X(2)
                    myX.a = 3
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
                struct X {
                    a: Int
                }
                fun test() {
                    val myX = X(2)
                    var otherX: mutable X = myX
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.reason shouldBe "cannot assign a immutable value to a mutable reference"
                }
        }

        "can be assigned to an immutable reference" {
            validateModule("""
                struct X {
                    a: Int
                }
                fun test() {
                    val myX = X(2)
                    val otherX: immutable X = myX
                }
            """.trimIndent()) should beEmpty()
        }
    }

    "mutability from use-site generics" - {
        "prohibits writes to immutable element" {
            validateModule("""
                struct A {
                    someVal: Int
                }
                struct B<T> {
                    genericVal: T
                }
                fun test() {
                    mutable val myB = B<immutable A>(A(3))
                    myB.genericVal = A(2)
                    myB.genericVal.someVal = 5
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting> {
                    it.statement.targetExpression.shouldBeInstanceOf<BoundMemberAccessExpression>().memberName shouldBe "someVal"
                }
        }
    }
})