package compiler.compiler

import compiler.compiler.binding.type.beAssignableTo
import compiler.compiler.binding.type.parseType
import compiler.compiler.negative.shouldFind
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.useValidModule
import compiler.compiler.negative.validateModule
import compiler.diagnostic.UseOfUninitializedClassMemberVariableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class OtherRegressions : FreeSpec({
    "generics" - {
        "long inference chains" {
            validateModule("""
                class Layer0<T0> {}
                class Layer1<T1> {
                    f1: Layer0<T1> = init
                }
                class Layer2<T2> {
                    f2: Layer1<T2> = init
                }
                class Layer3<T3> {
                    f3: Layer2<T3> = init
                }
                class Layer4<T4> {
                    f4: Layer3<T4> = init
                }
                fn step0<S0>(p: Layer0<S0>) {}
                fn step1<S1>(p: Layer1<S1>) {
                    step0(p.f1)
                }
                fn step2<S2>(p: Layer2<S2>) {
                    step1(p.f2)
                }
                fn step3<S3>(p: Layer3<S3>) {
                    step2(p.f3)
                }
                fn step4<S4>(p: Layer4<S4>) {
                    step3(p.f4)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "inference chain with nullability" {
            validateModule("""
                class Container<T> {
                    f: T? = init
                }
                fn triggerStep1<Y>(p: Container<Y>) {
                    triggerStep2(p.f)
                }
                fn triggerStep2<X>(p: X) {}
            """.trimIndent())
                .second
                .shouldBeEmpty()
        }
    }

    "diamond inheritance" - {
        "does not produce invocation ambiguity" {
            validateModule("""
                interface A {
                    fn foo(self)
                }
                interface B : A {}
                interface C : A {}
                interface D : B & C {}
                
                fn trigger(p: D) {
                    p.foo()
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "member var initializers can reference self (github issue #17)" - {
        "simple case" {
            validateModule("""
                class Foo {
                    a: S32 = 0
                    b: S32 = self.a + 5
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "are initialized in syntactic order, partial initialization is respected" {
            validateModule("""
                class Foo {
                    a: S32 = self.b + 5
                    b: S32 = 0
                }
            """.trimIndent())
                .shouldFind<UseOfUninitializedClassMemberVariableDiagnostic> {
                    it.member.name.value shouldBe "b"
                }
        }
    }

    "declaration-site variance".config(enabled = false) {
        // TODO: enable and fix, is broken since a LONG time
        val swCtx = useValidModule("""
            class C<out T> {}
        """.trimIndent())

        swCtx.parseType("read C<UWord>") should beAssignableTo(swCtx.parseType("read C<UWord?>"))
    }
})