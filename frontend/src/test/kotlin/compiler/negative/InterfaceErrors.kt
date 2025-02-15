package compiler.compiler.negative

import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.reportings.CyclicInheritanceReporting
import compiler.reportings.EntryNotAllowedInBaseTypeReporting
import compiler.reportings.MemberFunctionImplOnInterfaceReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf

class InterfaceErrors : FreeSpec({
    "constructors are not allowed" {
        validateModule("""
            interface Foo {
                constructor {
                }
            }
        """.trimIndent())
            .shouldReport<EntryNotAllowedInBaseTypeReporting> {
                it.typeKind shouldBe BoundBaseType.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BoundClassConstructor>()
            }
    }

    "destructors are not allowed" {
        validateModule("""
            interface Foo {
                destructor {
                }
            }
        """.trimIndent())
            .shouldReport<EntryNotAllowedInBaseTypeReporting> {
                it.typeKind shouldBe BoundBaseType.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BoundClassDestructor>()
            }
    }

    "member variables not allowed" {
        validateModule("""
            interface Foo {
                x: S32 = 3
            }
        """.trimIndent())
            .shouldReport<EntryNotAllowedInBaseTypeReporting> {
                it.typeKind shouldBe BoundBaseType.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BoundBaseTypeMemberVariable>()
            }
    }

    "member function implementations are not allowed" - {
        "actual virtual member function" {
            validateModule("""
                interface Foo {
                    fn bar(self: _) -> S32 = 42
                }
            """.trimIndent())
                .shouldReport<MemberFunctionImplOnInterfaceReporting>()
        }

        "static function without self argument" {
            validateModule("""
                interface Foo {
                    fn bar(bla: Any) -> S32 = 42
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "cyclic inheritance" - {
        "cycle size 1" {
            validateModule("""
                interface A : A {}
            """.trimIndent())
                .shouldReport<CyclicInheritanceReporting>()
        }

        "cycle size 2" {
            validateModule("""
                interface A : B {}
                interface B : A {}
            """.trimIndent())
                .shouldReport<CyclicInheritanceReporting>()
        }

        "cycle size 4" {
            validateModule("""
                interface A : D {}
                interface B : A {}
                interface C : B {}
                interface D : C {}
            """.trimIndent())
                .shouldReport<CyclicInheritanceReporting>()
        }
    }
})