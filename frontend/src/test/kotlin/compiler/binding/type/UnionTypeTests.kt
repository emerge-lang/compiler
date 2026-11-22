package compiler.compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundUnionTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.compiler.negative.shouldFind
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.shouldNotFind
import compiler.compiler.negative.validateModule
import compiler.diagnostic.IllegalSupertypeDiagnostic
import compiler.diagnostic.SimplifiableUnionTypeDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.WhenNotExhaustiveDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNot
import io.kotest.matchers.types.shouldBeInstanceOf

class UnionTypeTests : FreeSpec({
    val swCtx = validateModule("""
        interface T {}

        interface A : T {}
        interface B : T {}
        interface C {}

        class ConcreteA : A {}
        class ConcreteB : B {}
    """.trimIndent())
        .first

    "structure" - {
        "components" {
            val type = swCtx.parseType("A | B").shouldBeInstanceOf<BoundUnionTypeReference>()
            type.components.map { it.toString() } shouldBe listOf("read testmodule.A", "read testmodule.B")
            type.toString() shouldBe "read testmodule.A | read testmodule.B"
        }

        "an intersection binds tighter than a union" {
            val type = swCtx.parseType("A & B | C").shouldBeInstanceOf<BoundUnionTypeReference>()
            type.components shouldHaveSize 2
            type.components[0].shouldBeInstanceOf<BoundIntersectionTypeReference>().components.map { it.toString() } shouldBe listOf("read testmodule.A", "read testmodule.B")
            type.components[1].toString() shouldBe "read testmodule.C"
        }

        "nested unions are flattened" {
            val type = swCtx.parseType("A | B").closestCommonSupertypeWith(swCtx.parseType("C")).shouldBeInstanceOf<BoundUnionTypeReference>()
            type.components.map { it.toString() } shouldBe listOf("read testmodule.A", "read testmodule.B", "read testmodule.C")
        }

        "a nullable component makes the union nullable" {
            val type = swCtx.parseType("A | B?").shouldBeInstanceOf<NullableTypeReference>()
            val nested = type.nested.shouldBeInstanceOf<BoundUnionTypeReference>()
            nested.components.map { it.toString() } shouldBe listOf("read testmodule.A", "read testmodule.B")
            type.toString() shouldBe "(read testmodule.A | read testmodule.B)?"
        }

        "the mutability is what the components have in common" {
            swCtx.parseType("mut A | const B").mutability shouldBe TypeMutability.READONLY
            swCtx.parseType("mut A | mut B").mutability shouldBe TypeMutability.MUTABLE
            swCtx.parseType("mut A | read B").mutability shouldBe TypeMutability.READONLY
            swCtx.parseType("const A | const B").mutability shouldBe TypeMutability.IMMUTABLE
        }
    }

    "simplification" - {
        "a component that is a subtype of another is dropped" {
            swCtx.parseType("ConcreteA | A").shouldBeInstanceOf<BoundUnionTypeReference>().simplify().toString() shouldBe "read testmodule.A"
            swCtx.parseType("A | Nothing").shouldBeInstanceOf<BoundUnionTypeReference>().simplify().toString() shouldBe "read testmodule.A"
            swCtx.parseType("A | Any").shouldBeInstanceOf<BoundUnionTypeReference>().simplify().toString() shouldBe "read Any"
            swCtx.parseType("A | B | A").shouldBeInstanceOf<BoundUnionTypeReference>().simplify().toString() shouldBe "read testmodule.B | read testmodule.A"
        }

        "the kept component takes the mutability of the union" {
            swCtx.parseType("mut A | read ConcreteA").shouldBeInstanceOf<BoundUnionTypeReference>().simplify().toString() shouldBe "read testmodule.A"
        }

        "unrelated components stay" {
            val type = swCtx.parseType("A | B").shouldBeInstanceOf<BoundUnionTypeReference>()
            type.simplify() shouldBe type
        }

        "a simplifiable union written in source is reported" {
            validateModule("""
                interface A {}
                fn test(p: A | Nothing) {}
            """.trimIndent())
                .shouldFind<SimplifiableUnionTypeDiagnostic> {
                    it.simplerVersion.toString() shouldBe "read testmodule.A"
                }
        }
    }

    "subtyping" - {
        "a component is below the union" {
            swCtx.parseType("A") should beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("B") should beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("ConcreteA") should beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("C") shouldNot beAssignableTo(swCtx.parseType("A | B"))
        }

        "a union is below a type where each component is" {
            swCtx.parseType("A | B") should beAssignableTo(swCtx.parseType("T"))
            swCtx.parseType("A | B") should beAssignableTo(swCtx.parseType("Any"))
            swCtx.parseType("A | B") shouldNot beAssignableTo(swCtx.parseType("A"))
            swCtx.parseType("A | C") shouldNot beAssignableTo(swCtx.parseType("T"))
        }

        "a union is below a union where each component is" {
            swCtx.parseType("A | B") should beAssignableTo(swCtx.parseType("A | B | C"))
            swCtx.parseType("A | B") should beAssignableTo(swCtx.parseType("B | A"))
            swCtx.parseType("ConcreteA | ConcreteB") should beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("A | B | C") shouldNot beAssignableTo(swCtx.parseType("A | B"))
        }

        "mutability" {
            swCtx.parseType("mut A") should beAssignableTo(swCtx.parseType("read A | read B"))
            swCtx.parseType("read A") shouldNot beAssignableTo(swCtx.parseType("mut A | mut B"))
            swCtx.parseType("mut A | mut B") should beAssignableTo(swCtx.parseType("mut T"))
            swCtx.parseType("mut A | read B") shouldNot beAssignableTo(swCtx.parseType("mut T"))
        }

        "nullability" {
            swCtx.parseType("A?") shouldNot beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("A?") should beAssignableTo(swCtx.parseType("A | B?"))
            swCtx.parseType("A | B") should beAssignableTo(swCtx.parseType("A | B?"))
            swCtx.parseType("A | B?") shouldNot beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("A | B?") should beAssignableTo(swCtx.parseType("T?"))
        }

        "an intersection with a component below the union is below it" {
            swCtx.parseType("A & C") should beAssignableTo(swCtx.parseType("A | B"))
            swCtx.parseType("A & C") should beAssignableTo(swCtx.parseType("C | B"))
            swCtx.parseType("A & C") shouldNot beAssignableTo(swCtx.parseType("B | ConcreteB"))
        }

        "a union intersected with a type distributes, and is below the union" {
            val intersection = swCtx.parseType("A | B").intersect(swCtx.parseType("C")).shouldBeInstanceOf<BoundUnionTypeReference>()
            intersection.components shouldHaveSize 2
            intersection.components.forEach { it.shouldBeInstanceOf<BoundIntersectionTypeReference>() }
            intersection should beAssignableTo(swCtx.parseType("A | B"))
            intersection should beAssignableTo(swCtx.parseType("C"))
        }

        "a union intersected with one of its components is that component" {
            swCtx.parseType("ConcreteA | ConcreteB").intersect(swCtx.parseType("ConcreteA")).toString() shouldBe "read testmodule.ConcreteA"
        }
    }

    "common supertype" - {
        "of two unrelated types stays as it is" {
            swCtx.parseType("A").closestCommonSupertypeWith(swCtx.parseType("C")).shouldBeInstanceOf<RootResolvedTypeReference>()
        }

        "of a union and a type is the union of both" {
            val supertype = swCtx.parseType("A | B").closestCommonSupertypeWith(swCtx.parseType("C?"))
            swCtx.parseType("A | B") should beAssignableTo(supertype)
            swCtx.parseType("C?") should beAssignableTo(supertype)
            supertype.toString() shouldBe "(read testmodule.A | read testmodule.B | read testmodule.C)?"
        }
    }

    "in code" - {
        val declarations = """
            interface I {
                fn common(self) -> S32
            }
            class X : I {
                override fn common(self) -> S32 = 1
                fn onlyX(self) -> S32 = 10
            }
            class Y : I {
                override fn common(self) -> S32 = 2
            }
            class Z {}
            fn takeUnion(p: X | Y) {}
            fn takeX(p: X) {}
            fn takeI(p: I) {}
        """.trimIndent()

        "assigning a component" {
            validateModule("""
                $declarations
                fn test(x: X, y: Y) {
                    takeUnion(x)
                    takeUnion(y)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "assigning a non-component" {
            validateModule("""
                $declarations
                fn test(z: Z) {
                    takeUnion(z)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "assigning the union" {
            validateModule("""
                $declarations
                fn test(p: X | Y) {
                    takeI(p)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()

            validateModule("""
                $declarations
                fn test(p: X | Y) {
                    takeX(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "members every component has" {
            validateModule("""
                $declarations
                fn test(p: X | Y) -> S32 = p.common()
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "smart cast to a component" {
            validateModule("""
                $declarations
                fn test(p: X | Y) -> S32 {
                    if p is X {
                        takeX(p)
                        return p.onlyX()
                    }
                    return 0
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "type inference through a union" {
            validateModule("""
                $declarations
                fn identity<E>(e: E) -> E = e
                fn test(p: X | Y) -> X | Y = identity(p)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "returning a component for a union" {
            validateModule("""
                $declarations
                fn test(n: S32) -> X | Y | Z = if n == 0 X() else if n == 1 Y() else Z()
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a union cannot be inherited from" {
            validateModule("""
                $declarations
                class W : X | Y {}
            """.trimIndent())
                .shouldFind<IllegalSupertypeDiagnostic>()
        }

        "when exhaustiveness" - {
            "all components covered" {
                validateModule("""
                    $declarations
                    fn test(p: X | Y) -> S32 = when p {
                        is X -> 1
                        is Y -> 2
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "a component is missing" {
                validateModule("""
                    $declarations
                    fn test(p: X | Y | Z) -> S32 = when p {
                        is X -> 1
                        is Y -> 2
                    }
                """.trimIndent())
                    .shouldFind<WhenNotExhaustiveDiagnostic> {
                        it.missingClasses.map { c -> c.simpleName } shouldBe listOf("Z")
                        it.missesNull shouldBe false
                    }
            }

            "a union in a branch covers its components" {
                validateModule("""
                    $declarations
                    fn test(p: X | Y | Z) -> S32 = when p {
                        is X | Y -> 1
                        is Z -> 2
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "null needs a branch" {
                validateModule("""
                    $declarations
                    fn test(p: X | Y?) -> S32 = when p {
                        is X -> 1
                        is Y -> 2
                    }
                """.trimIndent())
                    .shouldFind<WhenNotExhaustiveDiagnostic> {
                        it.missingClasses shouldBe emptySet()
                        it.missesNull shouldBe true
                    }

                validateModule("""
                    $declarations
                    fn test(p: X | Y?) -> S32 = when p {
                        null -> 0
                        is X -> 1
                        is Y -> 2
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "an interface component covers its subtypes" {
                validateModule("""
                    $declarations
                    fn test(p: I | Z) -> S32 = when p {
                        is I -> 1
                        is Z -> 2
                    }
                """.trimIndent())
                    .shouldNotFind<WhenNotExhaustiveDiagnostic>()
            }
        }
    }
})
