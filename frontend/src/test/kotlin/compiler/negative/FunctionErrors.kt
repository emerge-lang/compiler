package compiler.compiler.negative

import compiler.diagnostic.AmbiguousInvocationDiagnostic
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.ExplicitInferTypeNotAllowedDiagnostic
import compiler.diagnostic.IllegalFunctionBodyDiagnostic
import compiler.diagnostic.InconsistentReceiverPresenceInOverloadSetDiagnostic
import compiler.diagnostic.MissingFunctionBodyDiagnostic
import compiler.diagnostic.MissingReturnValueDiagnostic
import compiler.diagnostic.MissingVariableTypeDiagnostic
import compiler.diagnostic.MultipleInheritanceIssueDiagnostic
import compiler.diagnostic.MultipleParameterDeclarationsDiagnostic
import compiler.diagnostic.OverloadSetHasNoDisjointParameterDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.ToplevelFunctionWithOverrideAttributeDiagnostic
import compiler.diagnostic.TypeParameterNameConflictDiagnostic
import compiler.diagnostic.UncertainTerminationDiagnostic
import compiler.diagnostic.UnknownTypeDiagnostic
import compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic
import compiler.diagnostic.UnsupportedCallingConventionDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.VarianceOnFunctionTypeParameterDiagnostic
import compiler.diagnostic.VarianceOnInvocationTypeArgumentDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf
import io.kotest.matchers.types.shouldBeInstanceOf

class FunctionErrors : FreeSpec({
    "body" - {
        "external function cannot have body" {
            validateModule(
                """
                external(C) fn foo() -> S32 {
                    return 3
                }
            """.trimIndent()
            )
                .shouldFind<IllegalFunctionBodyDiagnostic>()
        }

        "non-external function must have body" {
            validateModule(
                """
                fn foo() -> S32
            """.trimIndent()
            )
                .shouldFind<MissingFunctionBodyDiagnostic>()
        }
    }

    "parameters" - {
        "function parameters must have explicit types" {
            validateModule(
                """
                fn foo(bar) = 3
            """.trimIndent()
            )
                .shouldFind<MissingVariableTypeDiagnostic>() {
                    it.parameter.name.value shouldBe "bar"
                }
        }

        "parameter name duplicate" {
            validateModule("""
                fn foo(a: S32, a: Bool, b: S32) {}
            """.trimIndent())
                    .shouldFind<MultipleParameterDeclarationsDiagnostic> {
                        it.firstDeclaration.name.value shouldBe "a"
                        it.additionalDeclaration.name.value shouldBe "a"
                    }
        }

        "explicit type inference on parameters is not allowed" {
            validateModule("""
                fn foo(p: _) {}
            """.trimIndent())
                .shouldFind<ExplicitInferTypeNotAllowedDiagnostic>()
        }
    }

    "unknown declared return type" {
        validateModule("""
            fn a() -> Foo {
                return 0
            }
        """.trimIndent())
            .shouldFind<UnknownTypeDiagnostic>()
    }

    "unknown declared receiver type" {
        validateModule("""
            fn a(self: Foo) {
            }
        """.trimIndent())
            .shouldFind<UnknownTypeDiagnostic>()
    }

    "overloads" - {
        "calling non-existent function overload" {
            // disabled because with the overload resolution algorithm not fleshed out completely
            // this test cannot run
            validateModule("""
                class A {}
                class B {}
                fn foo(p1: A) {}
                fn foo(p1: B) {}            
                fn test() {
                    foo(true)
                }
            """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic>()
        }

        "overload-set with single non-disjoint parameter is not valid" {
            validateModule("""
                fn foo(a: Number) {}
                fn foo(a: S32) {}
            """.trimIndent())
                .shouldFind<OverloadSetHasNoDisjointParameterDiagnostic>()
        }

        "overload-set with multiple parameters, none of which has disjoint types, is not valid" {
            validateModule("""
                fn foo(a: S32, b: Any) {}
                fn foo(a: Any, b: S32) {}
            """.trimIndent())
                .shouldFind<OverloadSetHasNoDisjointParameterDiagnostic>()
        }

        "overload set with multiple parameters, only one of which has disjoint types, is valid" {
            validateModule("""
                fn foo(a: Any, b: Any, c: S32, d: Any) {}
                fn foo(a: S32, b: String, c: String, d: S32) {}
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "ambiguous invocation involving valid overload sets" {
            validateModule("""
                fn println(p: Any) {}
                
                fn main() {
                    println("Hello, World!")
                }
            """.trimIndent())
                .shouldFind<AmbiguousInvocationDiagnostic>()
        }

        "no argument assignable to a disjointly typed parameter" {
            validateModule("""
                class A {}
                class B {}
                fn foo(disjoint: A, p: S32) {}
                fn foo(disjoint: B, p: S32) {}
                fn test() {
                    foo(0, 0)
                }
            """.trimIndent())
                .shouldFind<UnresolvableFunctionOverloadDiagnostic>()
        }

        "argument not assignable to non-disjointly typed parameter" {
            val (_, diagnostics) = validateModule("""
                class A {}
                class B {}
                fn foo(disjoint: A, p1: S32, p2: S32) {}
                fn foo(disjoint: B, p1: S32, p2: S32) {}
                fn test() {
                    foo(A(), "123", B())
                }
            """.trimIndent())

            diagnostics should haveSize(2)
            diagnostics.forOne {
                it.shouldBeInstanceOf<ValueNotAssignableDiagnostic>().also {
                    it.sourceType.toString() shouldBe "const String"
                    it.targetType.toString() shouldBe "const S32"
                }
            }
            diagnostics.forOne {
                it.shouldBeInstanceOf<ValueNotAssignableDiagnostic>().also {
                    it.sourceType.toString() shouldBe "exclusive testmodule.B"
                    it.targetType.toString() shouldBe "const S32"
                }
            }
        }

        "presence of receiver must be consistent" {
            validateModule("""
                fn foo(self: S32, p2: String) {}
                fn foo(p1: S32, p2: S32) {}
            """.trimIndent())
                .shouldFind<InconsistentReceiverPresenceInOverloadSetDiagnostic>()
        }

        "inheritance induced" - {
            "inheriting from two types creates ambiguous overload" {
                validateModule("""
                    interface A {
                        fn foo(self, p1: S32)
                    }
                    interface B {
                        fn foo(self, p1: Any)
                    }
                    interface Irrelevant {
                        fn bar(self)
                    }
                    class C : A & B & Irrelevant {
                        override fn bar(self) {}
                    }
                """.trimIndent())
                    .shouldFind<MultipleInheritanceIssueDiagnostic> {
                        it.base should beInstanceOf<OverloadSetHasNoDisjointParameterDiagnostic>()
                        it.conflictOnSubType.canonicalName.toString() shouldBe "testmodule.C"
                        it.contributingSuperTypes.map { it.canonicalName.simpleName }.toSet() shouldBe setOf("A", "B")
                    }
            }

            "inherited overload disjointness is reported only once" {
                val results = validateModule("""
                    interface Problematic {
                        fn foo(self, p1: S32)
                        fn foo(self, p1: Any)
                    }
                    interface Innocent : Problematic {}
                """.trimIndent())
                results.second.count { it.severity >= Diagnostic.Severity.ERROR } shouldBe 1
                results.shouldFind<OverloadSetHasNoDisjointParameterDiagnostic>()
            }
        }
    }

    "calling a function that doesn't exist by name" {
        validateModule("""
            fn test() {
                foo(true)
            }
        """.trimIndent())
            .shouldFind<UnresolvableFunctionOverloadDiagnostic>()
    }

    "termination" - {
        "empty body in non-unit function" {
            validateModule("""
                fn a() -> S32 {
                }
            """.trimIndent())
                .shouldFind<UncertainTerminationDiagnostic>()
        }

        "return type mismatch" - {
            "on return statement" {
                validateModule("""
                    fn a() -> S32 {
                        return true
                    }
                """.trimIndent())
                    .shouldFind<ReturnTypeMismatchDiagnostic>()
            }

            "on single-expression body" {
                validateModule("""
                    fn a() -> S32 = false
                """.trimIndent())
                    .shouldFind<ReturnTypeMismatchDiagnostic>()
            }
        }

        "value-less return from" - {
            "from function that doesn't declare return type" {
                validateModule("""
                    fn a() {
                        return
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "from function that declares Unit return type" {
                validateModule("""
                    fn a() -> Unit {
                        return
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "from function that declares non-unit return type" {
                validateModule("""
                    fn a() -> S32 {
                        return
                    }
                """.trimIndent())
                    .shouldFind<MissingReturnValueDiagnostic>()
            }
        }

        "if where only then returns" {
            validateModule("""
                fn a(p: Bool) -> S32 {
                    if p {
                        return 0
                    } else {
                    }
                }
            """.trimIndent())
                .shouldFind<UncertainTerminationDiagnostic>()
        }

        "if where only else returns" {
            validateModule("""
                fn a(p: Bool) -> S32 {
                    if p {
                    } else {
                        return 0
                    }
                }
            """.trimIndent())
                .shouldFind<UncertainTerminationDiagnostic>()
        }

        // TODO: if where only one branch throws, one test for then and else each
        // TODO: loop where the termination (return + throw) is in the loop body and the condition is not always true
    }

    "generics" - {
        "unresolvable bound on type parameter" {
            validateModule("""
                fn foo<T : Bla>() {}
            """.trimIndent())
                .shouldFind<UnknownTypeDiagnostic> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }

        "in variance on type parameter" {
            validateModule("""
                fn foo<in T : String>() {}
            """.trimIndent())
                .shouldFind<VarianceOnFunctionTypeParameterDiagnostic> {
                    it.parameter.name.value shouldBe "T"
                }
        }

        "out variance on type parameter" {
            validateModule("""
                fn foo<out T : String>() {}
            """.trimIndent())
                .shouldFind<VarianceOnFunctionTypeParameterDiagnostic> {
                    it.parameter.name.value shouldBe "T"
                }
        }

        "type parameter duplication" {
            validateModule("""
                fn foo<T, T>() {}
            """.trimIndent())
                .shouldFind<TypeParameterNameConflictDiagnostic>()
        }

        "type parameter name collides with top level type" {
            validateModule("""
                fn foo<S32>() {}
            """.trimIndent())
                .shouldFind<TypeParameterNameConflictDiagnostic>()
        }

        "variance on invocation" {
            validateModule("""
                fn foo<X>() {}
                fn test() {
                    foo::<in X>()
                }
            """.trimIndent())
                .shouldFind<VarianceOnInvocationTypeArgumentDiagnostic>()

            validateModule("""
                fn foo<X>() {}
                fn test() {
                    foo::<out X>()
                }
            """.trimIndent())
                .shouldFind<VarianceOnInvocationTypeArgumentDiagnostic>()
        }
    }

    "toplevel specific" - {
        "cannot override" {
            validateModule("""
                override fn test() {
                }
            """.trimIndent())
                .shouldFind<ToplevelFunctionWithOverrideAttributeDiagnostic>()
        }
    }

    "ffi" - {
        "unsupported FFI" {
            validateModule("""
                override external(Rust) fn test()
            """.trimIndent())
                .shouldFind<UnsupportedCallingConventionDiagnostic>()
        }
    }
})