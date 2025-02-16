package compiler.compiler.negative

import compiler.ast.type.TypeMutability
import compiler.binding.context.ExecutionScopedCTContext
import compiler.reportings.AbstractInheritedFunctionNotImplementedReporting
import compiler.reportings.IllegalMixinRepetitionReporting
import compiler.reportings.MixinNotAllowedReporting
import compiler.reportings.ObjectUsedBeforeMixinInitializationReporting
import compiler.reportings.UnusedMixinReporting
import compiler.reportings.ValueNotAssignableReporting
import compiler.reportings.VariableUsedAfterLifetimeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forExactly
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

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

    "unused mixin" - {
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

    "illegal mixin repetition" - {
        "only in then-branch of if" {
            validateModule("""
                interface I {
                    fn test(self) -> S32
                }
                intrinsic fn provideSomeI() -> exclusive I
                intrinsic fn flipCoin() -> Bool
                class Bar : I {
                    constructor {
                        if flipCoin() {
                            mixin provideSomeI()
                        } else {
                            
                        }
                    }
                }
            """.trimIndent())
                .shouldReport<IllegalMixinRepetitionReporting>()
        }

        "only in else-branch of if" {
            validateModule("""
                interface I {
                    fn test(self) -> S32
                }
                intrinsic fn provideSomeI() -> exclusive I
                intrinsic fn flipCoin() -> Bool
                class Bar : I {
                    constructor {
                        if flipCoin() {
                            
                        } else {
                            mixin provideSomeI()
                        }
                    }
                }
            """.trimIndent())
                .shouldReport<IllegalMixinRepetitionReporting>()
        }

        "in two branches of if" {
            validateModule("""
                interface I {
                    fn test(self) -> S32
                }
                intrinsic fn provideSomeI() -> exclusive I
                intrinsic fn flipCoin() -> Boolean
                class Bar : I {
                    constructor {
                        mixedIn = provideSomeI()
                        if flipCoin() {
                            mixin mixedIn                            
                        } else {
                            mixin mixedIn
                        }
                    }
                }
            """.trimIndent())
                .second
                .forExactly(2) {
                    it.shouldBeInstanceOf<IllegalMixinRepetitionReporting>()
                    it.repetition shouldBe ExecutionScopedCTContext.Repetition.MAYBE
                }
        }

        "in while" {
            validateModule("""
                interface I {
                    fn test(self) -> S32
                }
                intrinsic fn provideSomeI() -> exclusive I
                intrinsic fn flipCoin() -> Boolean
                class Bar : I {
                    constructor {
                        while (flipCoin()) {
                            mixin provideSomeI()
                        }
                    }
                }
            """.trimIndent())
                .shouldReport<IllegalMixinRepetitionReporting>()
        }

        "in try" {
            validateModule("""
                interface I {
                    fn test(self) -> S32
                }
                intrinsic fn provideSomeI() -> exclusive I
                class Bar : I {
                    constructor {
                        try {
                            mixin provideSomeI()
                        }
                        catch e {}
                    }
                }
            """.trimIndent())
                .shouldReport<IllegalMixinRepetitionReporting>()
        }

        "in catch" {
            validateModule("""
                interface I {
                    fn test(self) -> S32
                }
                intrinsic fn provideSomeI() -> exclusive I
                fn doSomethingRisky() -> Bool = true
                class Bar : I {
                    constructor {
                        try {
                            doSomethingRisky()
                        }
                        catch e {
                            mixin provideSomeI()
                        }
                    }
                }
            """.trimIndent())
                .shouldReport<IllegalMixinRepetitionReporting>()
        }
    }
})