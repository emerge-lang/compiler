package compiler.compiler.negative

import compiler.ast.type.NamedTypeReference
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.compiler.binding.type.parseTypeArgument
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.WildcardTypeArgumentOnInvocationDiagnostic
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.Matcher
import io.kotest.matchers.MatcherResult
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNot

class VarianceErrors : FreeSpec({
    val swCtx = validateModule("""
        interface Parent {}
        interface Child : Parent {}
    """.trimIndent()).first

    val ctCtx = swCtx.getPackage(CanonicalElementName.Package(listOf("testmodule")))!!.sourceFiles.single().context

    fun arrayOf(element: BoundTypeArgument): BoundTypeReference = RootResolvedTypeReference(
        ctCtx,
        NamedTypeReference(swCtx.array.simpleName),
        swCtx.getPackage(EmergeConstants.CoreModule.NAME)!!.resolveBaseType("Array")!!,
        listOf(element),
    )

    fun beAssignableTo(target: BoundTypeArgument): Matcher<BoundTypeArgument> = object : Matcher<BoundTypeArgument> {
        override fun test(value: BoundTypeArgument): MatcherResult {
            val sourceType = arrayOf(value)
            val targetType = arrayOf(target)
            val error = sourceType.evaluateAssignabilityTo(targetType, Span.UNKNOWN)
            return object : MatcherResult {
                override fun failureMessage() = "$sourceType should be assignable to $targetType, but its not: ${error?.reason}"
                override fun negatedFailureMessage() = "$sourceType should not be assignable to $targetType, but it is"
                override fun passed() = error == null
            }
        }
    }

    val exactParent = swCtx.parseTypeArgument("Parent")
    val inParent = swCtx.parseTypeArgument("in Parent")
    val outParent = swCtx.parseTypeArgument("out Parent")
    val exactChild = swCtx.parseTypeArgument("Child")
    val inChild = swCtx.parseTypeArgument("in Child")
    val outChild = swCtx.parseTypeArgument("out Child")

    "same type" - {
        "Child to Child" {
            exactChild should beAssignableTo(exactChild)
        }

        "Child to in Child" {
            exactChild should beAssignableTo(inChild)
        }

        "Child to out Child" {
            exactChild should beAssignableTo(outChild)
        }

        "in Child to Child" {
            inChild shouldNot beAssignableTo(exactChild)
        }

        "in Child to in Child" {
            inChild should beAssignableTo(inChild)
        }

        "in Child to out Child" {
            inChild shouldNot beAssignableTo(outChild)
        }

        "out Child to Child" {
            outChild shouldNot beAssignableTo(exactChild)
        }

        "out Child to in Child" {
            outChild shouldNot beAssignableTo(inChild)
        }

        "out Child to out Child" {
            outChild should beAssignableTo(outChild)
        }
    }

    "assign child type to parent reference" - {
        "Child to Parent" {
            exactChild shouldNot beAssignableTo(exactParent)
        }

        "Child to in Parent" {
            exactChild shouldNot beAssignableTo(inParent)
        }

        "Child to out Parent" {
            exactChild should beAssignableTo(outParent)
        }

        "in Child to Parent" {
            inChild shouldNot beAssignableTo(exactParent)
        }

        "in Child to in Parent" {
            inChild shouldNot beAssignableTo(inParent)
        }

        "in Child to out Parent" {
            inChild shouldNot beAssignableTo(outParent)
        }

        "out Child to Parent" {
            outChild shouldNot beAssignableTo(exactParent)
        }

        "out Child to in Parent" {
            outChild shouldNot beAssignableTo(inParent)
        }

        "out Child to out Parent" {
            outChild should beAssignableTo(outParent)
        }
    }

    "assign parent type to child reference" - {
        "Parent to Child" {
            exactParent shouldNot beAssignableTo(exactChild)
        }

        "Parent to in Child" {
            exactParent should beAssignableTo(inChild)
        }

        "Parent to out Child" {
            exactParent shouldNot beAssignableTo(outChild)
        }

        "in Parent to Child" {
            inParent shouldNot beAssignableTo(exactChild)
        }

        "in Parent to in Child" {
            inParent should beAssignableTo(inChild)
        }

        "in Parent to out Child" {
            inParent shouldNot beAssignableTo(outChild)
        }

        "out Parent to Child" {
            outParent shouldNot beAssignableTo(exactChild)
        }

        "out Parent to in Child" {
            outParent shouldNot beAssignableTo(inChild)
        }

        "out Parent to out Child" {
            outParent shouldNot beAssignableTo(outChild)
        }
    }

    "in-variant type argument assumes type read Any? in out-position" {
        validateModule("""
            interface A {}
            interface B : A {}
            class C<T : A> {
                p: T
            }
            fn test<T : A>() {
                a: C<in B> = C(2)
                var x: T
                set x = a.p
            }
        """.trimIndent())
            .shouldFind<ValueNotAssignableDiagnostic> {
                it.sourceType.toString() shouldBe "read Any?"
                it.targetType.toString() shouldBe "T"
            }
    }

    "wildcard type arguments are not valid in function invocations" {
        validateModule("""
            interface B {}
            fn subject<T : B>(p: T) -> T = p
            fn trigger() {
                subject::<*>(3)
            }
        """.trimIndent())
            .shouldFind<WildcardTypeArgumentOnInvocationDiagnostic>()
    }
})