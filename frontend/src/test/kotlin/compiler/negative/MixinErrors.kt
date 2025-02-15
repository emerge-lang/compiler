package compiler.compiler.negative

import compiler.ast.type.TypeMutability
import compiler.reportings.AbstractInheritedFunctionNotImplementedReporting
import compiler.reportings.MixinNotAllowedReporting
import compiler.reportings.ObjectUsedBeforeMixinInitializationReporting
import compiler.reportings.UnusedMixinReporting
import compiler.reportings.ValueNotAssignableReporting
import compiler.reportings.VariableUsedAfterLifetimeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class MixinErrors : FreeSpec({
    "mixin in top level fn" {
        validateModule("""
            class Foo {}
            fn test() {
                mixin Foo
            }
        """.trimIndent())
            .shouldReport<MixinNotAllowedReporting>()
    }

    "mixin in member function" {
        validateModule("""
            class Foo {}
            class Bar {
                fn test() {
                    mixin Foo
                }
            }
        """.trimIndent())
            .shouldReport<MixinNotAllowedReporting>()
    }

    "mixin must be a exclusive value" {
        validateModule("""
            interface I {
                fn test(self) -> S32
            }
            class Foo : I {
                override fn test(self) = 3
            }
            class Bar : I {
                constructor {
                    mixin Foo as read Foo
                }
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting> {
                it.targetType.mutability shouldBe TypeMutability.EXCLUSIVE
                it.sourceType.mutability shouldBe TypeMutability.READONLY
            }
    }

    "mixin must not be null" {
        validateModule("""
            interface I {
                fn test(self) -> S32
            }
            intrinsic fn provideSomeI() -> exclusive I?
            class Bar : I {
                constructor {
                    mixin provideSomeI()
                }
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting> {
                it.sourceType.isNullable shouldBe true
                it.targetType.isNullable shouldBe false
            }
    }

    "mixin is captured" {
        validateModule("""
            interface I {
                fn test(self) -> S32
            }
            intrinsic fn provideSomeI() -> exclusive I
            intrinsic fn useSomeI(borrow value: read I)
            class Bar : I {
                constructor {
                    mixinValue: exclusive _ = provideSomeI()
                    mixin mixinValue
                    useSomeI(mixinValue)
                }
            }
        """.trimIndent())
            .shouldReport<VariableUsedAfterLifetimeReporting> {
                it.variable.name.value shouldBe "mixinValue"
            }
    }

    "use of self before all mixins are initialized" {
        validateModule("""
            interface I {
                fn test(self) -> S32
            }
            intrinsic fn provideSomeI() -> exclusive I
            class Bar : I {
                constructor { 
                    self.bla()
                    mixin provideSomeI()
                }
                
                fn bla(self) {}
            }
        """.trimIndent())
            .shouldReport<ObjectUsedBeforeMixinInitializationReporting>()
    }

    "indirect inheritance" - {
        "mixin can handle indirectly inherited fn" {
            validateModule(
                """
                interface A {
                    fn test(self) -> S32
                }
                interface B : A { }
                intrinsic fn provideSomeB() -> exclusive B
                class C : B {
                    constructor {
                        mixin provideSomeB()
                    }
                }
            """.trimIndent()
            )
                .shouldHaveNoDiagnostics()
        }
    }

    "unused mixing" - {
        "no applicable type" {
            validateModule("""
                interface A {
                    fn test(self) -> S32
                }
                class M {
                    intrinsic fn bla(self) -> Bool
                }
                
                class Test : A {
                    constructor {
                        mixin M()
                    }
                }
            """.trimIndent())
                .ignore<AbstractInheritedFunctionNotImplementedReporting>()
                .shouldReport<UnusedMixinReporting>()
        }

        "override present" {
            validateModule("""
                interface A {
                    fn test(self) -> S32
                }
                class M : A {
                    fn test(self) -> S32 = 3
                }
                
                class Test : A {
                    constructor {
                        mixin M()
                    }
                    
                    override fn test(self) -> S32 = 1
                }
            """.trimIndent())
                .shouldReport<UnusedMixinReporting>()
        }
    }
})