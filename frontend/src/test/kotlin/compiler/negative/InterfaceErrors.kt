package compiler.compiler.negative

import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.diagnostic.CyclicInheritanceDiagnostic
import compiler.diagnostic.EntryNotAllowedInBaseTypeDiagnostic
import compiler.diagnostic.MemberFunctionImplOnInterfaceDiagnostic
import compiler.diagnostic.UnsupportedDeclarationSiteVarianceDiagnostic
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
            .shouldFind<EntryNotAllowedInBaseTypeDiagnostic> {
                it.typeKind shouldBe BoundBaseType.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BaseTypeConstructorDeclaration>()
            }
    }

    "destructors are not allowed" {
        validateModule("""
            interface Foo {
                destructor {
                }
            }
        """.trimIndent())
            .shouldFind<EntryNotAllowedInBaseTypeDiagnostic> {
                it.typeKind shouldBe BoundBaseType.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BaseTypeDestructorDeclaration>()
            }
    }

    "member variables not allowed" {
        validateModule("""
            interface Foo {
                x: S32 = 3
            }
        """.trimIndent())
            .shouldFind<EntryNotAllowedInBaseTypeDiagnostic> {
                it.typeKind shouldBe BoundBaseType.Kind.INTERFACE
                it.violatingEntry should beInstanceOf<BaseTypeMemberVariableDeclaration>()
            }
    }

    "member function implementations are not allowed" - {
        "actual virtual member function" {
            validateModule("""
                interface Foo {
                    fn bar(self: _) -> S32 = 42
                }
            """.trimIndent())
                .shouldFind<MemberFunctionImplOnInterfaceDiagnostic>()
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
                .shouldFind<CyclicInheritanceDiagnostic>()
        }

        "cycle size 2" {
            validateModule("""
                interface A : B {}
                interface B : A {}
            """.trimIndent())
                .shouldFind<CyclicInheritanceDiagnostic>()
        }

        "cycle size 4" {
            validateModule("""
                interface A : D {}
                interface B : A {}
                interface C : B {}
                interface D : C {}
            """.trimIndent())
                .shouldFind<CyclicInheritanceDiagnostic>()
        }
    }

    "generics" - {
        "declaration-site variance is not supported" {
            validateModule("""
                interface Foo<out T> {}
            """.trimIndent())
                .shouldFind<UnsupportedDeclarationSiteVarianceDiagnostic>()

            validateModule("""
                interface Foo<in T> {}
            """.trimIndent())
                .shouldFind<UnsupportedDeclarationSiteVarianceDiagnostic>()
        }
    }
})