package compiler.compiler.negative

import compiler.CoreIntrinsicsModule
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance.IN
import compiler.ast.type.TypeVariance.OUT
import compiler.ast.type.TypeVariance.UNSPECIFIED
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.compiler.ast.type.getTestType
import compiler.lexer.SourceLocation
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.Matcher
import io.kotest.matchers.MatcherResult
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNot
import io.mockk.mockk

class VarianceErrors : FreeSpec({
    val swCtx = validateModule("""
        interface Parent {}
        interface Child : Parent {}
    """.trimIndent()).first

    val Parent = swCtx.getTestType("Parent")
    val Child = swCtx.getTestType("Child")
    val ctCtx = Parent.context

    fun varIn(t: BoundBaseTypeDefinition) = BoundTypeArgument(ctCtx, mockk(), IN, t.baseReference)
    fun varOut(t: BoundBaseTypeDefinition) = BoundTypeArgument(ctCtx, mockk(), OUT, t.baseReference)
    fun varExact(t: BoundBaseTypeDefinition) = BoundTypeArgument(ctCtx, mockk(), UNSPECIFIED, t.baseReference)

    fun arrayOf(element: BoundTypeArgument): BoundTypeReference = RootResolvedTypeReference(
        TypeReference("Array"),
        swCtx.getPackage(CoreIntrinsicsModule.NAME)!!.resolveBaseType("Array")!!,
        listOf(element),
    )

    fun beAssignableTo(target: BoundTypeArgument): Matcher<BoundTypeArgument> = object : Matcher<BoundTypeArgument> {
        override fun test(value: BoundTypeArgument): MatcherResult {
            val sourceType = arrayOf(value)
            val targetType = arrayOf(target)
            val error = sourceType.evaluateAssignabilityTo(targetType, SourceLocation.UNKNOWN)
            return object : MatcherResult {
                override fun failureMessage() = "$sourceType should be assignable to $targetType, but its not: ${error?.reason}"
                override fun negatedFailureMessage() = "$sourceType should not be assignable to $targetType, but it is"
                override fun passed() = error == null
            }
        }
    }

    "same type" - {
        "Child to Child" {
            varExact(Child) should beAssignableTo(varExact(Child))
        }

        "Child to in Child" {
            varExact(Child) should beAssignableTo(varIn(Child))
        }

        "Child to out Child" {
            varExact(Child) should beAssignableTo(varOut(Child))
        }

        "in Child to Child" {
            varIn(Child) shouldNot beAssignableTo(varExact(Child))
        }

        "in Child to in Child" {
            varIn(Child) should beAssignableTo(varIn(Child))
        }

        "in Child to out Child" {
            varIn(Child) shouldNot beAssignableTo(varOut(Child))
        }

        "out Child to Child" {
            varOut(Child) shouldNot beAssignableTo(varExact(Child))
        }

        "out Child to in Child" {
            varOut(Child) shouldNot beAssignableTo(varIn(Child))
        }

        "out Child to out Child" {
            varOut(Child) should beAssignableTo(varOut(Child))
        }
    }

    "assign child type to parent reference" - {
        "Child to Parent" {
            varExact(Child) shouldNot beAssignableTo(varExact(Parent))
        }

        "Child to in Parent" {
            varExact(Child) shouldNot beAssignableTo(varIn(Parent))
        }

        "Child to out Parent" {
            varExact(Child) should beAssignableTo(varOut(Parent))
        }

        "in Child to Parent" {
            varIn(Child) shouldNot beAssignableTo(varExact(Parent))
        }

        "in Child to in Parent" {
            varIn(Child) shouldNot beAssignableTo(varIn(Parent))
        }

        "in Child to out Parent" {
            varIn(Child) shouldNot beAssignableTo(varOut(Parent))
        }

        "out Child to Parent" {
            varOut(Child) shouldNot beAssignableTo(varExact(Parent))
        }

        "out Child to in Parent" {
            varOut(Child) shouldNot beAssignableTo(varIn(Parent))
        }

        "out Child to out Parent" {
            varOut(Child) should beAssignableTo(varOut(Parent))
        }
    }

    "assign parent type to child reference" - {
        "Parent to Child" {
            varExact(Parent) shouldNot beAssignableTo(varExact(Child))
        }

        "Parent to in Child" {
            varExact(Parent) should beAssignableTo(varIn(Child))
        }

        "Parent to out Child" {
            varExact(Parent) shouldNot beAssignableTo(varOut(Child))
        }

        "in Parent to Child" {
            varIn(Parent) shouldNot beAssignableTo(varExact(Child))
        }

        "in Parent to in Child" {
            varIn(Parent) should beAssignableTo(varIn(Child))
        }

        "in Parent to out Child" {
            varIn(Parent) shouldNot beAssignableTo(varOut(Child))
        }

        "out Parent to Child" {
            varOut(Parent) shouldNot beAssignableTo(varExact(Child))
        }

        "out Parent to in Child" {
            varOut(Parent) shouldNot beAssignableTo(varIn(Child))
        }

        "out Parent to out Child" {
            varOut(Parent) shouldNot beAssignableTo(varOut(Child))
        }
    }

    "in-variant type argument assumes type readonly Any? in out-position" {
        validateModule("""
                class A<T : Number> {
                    p: T
                }
                fun test<T : Number>() {
                    a: A<in S32> = A(2)
                    var x: T
                    set x = a.p
                }
            """.trimIndent())
            .shouldReport<ValueNotAssignableReporting> {
                it.sourceType.toString() shouldBe "readonly Any?"
                it.targetType.toString() shouldBe "T"
            }
    }
})