package compiler.compiler.binding.type

import compiler.binding.AccessorKind
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.compiler.negative.shouldFind
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import compiler.diagnostic.AmbiguousInvocationDiagnostic
import compiler.diagnostic.AmbiguousMemberVariableAccessDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class IntersectionTypeTests : FreeSpec({
    val swCtx = validateModule("""
        interface T {}
        
        interface A {}
        interface B {}
        interface C {}
        
        class ConcreteA {}
        class ConcreteB {}
    """.trimIndent())
        .first

    "simplification" - {
        "read T & mut Any simplifies to mut T" {
            val type = swCtx.parseType("read T & mut Any")
            val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }

        "mut T? & read Any? simplifies to mut T?" {
            val type = swCtx.parseType("mut T? & read Any?")
            val simplified = type
                .shouldBeInstanceOf<NullableTypeReference>()
                .nested
                .shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }

        "read T? & mut Any simplifies to mut T" {
            val type = swCtx.parseType("read T? & mut Any")
            val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }

        "intersection of two class types is nothing" - {
            "simple case" {
                val type = swCtx.parseType("ConcreteA & T & ConcreteB")
                val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
                simplified.toString() shouldBe "read Nothing"
            }

            "retains compound mutability" {
                val type = swCtx.parseType("mut ConcreteA & T & ConcreteB")
                val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
                simplified.toString() shouldBe "mut Nothing"

                val type2 = swCtx.parseType("mut ConcreteA & T & const ConcreteB")
                val simplified2 = type2.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
                simplified2.toString() shouldBe "exclusive Nothing"
            }

            "retains compound Nullability" {
                val type = swCtx.parseType("ConcreteA? & ConcreteB?")
                val simplified = type
                    .shouldBeInstanceOf<NullableTypeReference>()
                    .nested
                    .shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
                simplified.toString() shouldBe "read Nothing"
            }
        }
    }

    "subtyping" - {
        "non-compound target" {
            swCtx.parseType("A & B") should beAssignableTo(swCtx.parseType("A"))
            swCtx.parseType("A & B") should beAssignableTo(swCtx.parseType("B"))
        }

        "compound target" {
            swCtx.parseType("A & B & C") should beAssignableTo(swCtx.parseType("A & B"))
            swCtx.parseType("A & B & C") should beAssignableTo(swCtx.parseType("A & C"))
            swCtx.parseType("A & B & C") should beAssignableTo(swCtx.parseType("B & C"))
        }
    }

    "member ambiguity" - {
        "functions" {
            validateModule("""
                interface A {
                    fn foo(self)
                }
                interface B {
                    fn foo(self)
                }
                fn test(p: A & B) {
                    p.foo()
                }
            """.trimIndent())
                .shouldFind<AmbiguousInvocationDiagnostic>()

            // disambiguating shouldn't complain about an unnecessary cast
            validateModule("""
                interface A {
                    fn foo(self)
                }
                interface B {
                    fn foo(self)
                }
                fn test(p: A & B) {
                    (p as A).foo()
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "members" - {
            "read" {
                validateModule("""
                    class A {
                        x: S32 = 0
                    }
                    class B {
                        x: S32 = 0
                    }
                    fn trigger(p: A & B) -> S32 = p.x
                """.trimIndent())
                    .shouldFind<AmbiguousMemberVariableAccessDiagnostic> {
                        it.accessKind shouldBe AccessorKind.Read
                        it.memberVariableName shouldBe "x"
                    }
            }

            "write" {
                validateModule("""
                    class A {
                        x: S32 = 0
                    }
                    class B {
                        x: S32 = 0
                    }
                    fn trigger(p: mut A & mut B) {
                        set p.x = 2
                    }
                """.trimIndent())
                    .shouldFind<AmbiguousMemberVariableAccessDiagnostic> {
                        it.accessKind shouldBe AccessorKind.Write
                        it.memberVariableName shouldBe "x"
                    }
            }
        }
    }
})