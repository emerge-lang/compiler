package compiler.compiler.negative

import compiler.binding.type.GenericTypeReference
import compiler.diagnostic.MissingTypeArgumentDiagnostic
import compiler.diagnostic.SimplifiableIntersectionTypeDiagnostic
import compiler.diagnostic.SuperfluousTypeArgumentsDiagnostic
import compiler.diagnostic.TypeArgumentOutOfBoundsDiagnostic
import compiler.diagnostic.TypeArgumentVarianceMismatchDiagnostic
import compiler.diagnostic.TypeArgumentVarianceSuperfluousDiagnostic
import compiler.diagnostic.UnsatisfiableTypeVariableConstraintsDiagnostic
import compiler.diagnostic.UnsupportedTypeUsageVarianceDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class TypeErrors : FreeSpec({
    "generics" - {
        "assign to out-variant type parameter" {
            validateModule("""
                interface A {}
                class B : A {}
                class X<T> {
                    var prop: T = init
                }
                
                fn foo() {
                    var myX: X<out A> = X(B())
                    set myX.prop = B()
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "assignment of generically typed value to directly typed variable" {
            validateModule("""
                fn foo<T>(p: T) {
                    x: Any? = p
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "assignment of directly typed value to generically typed variable" {
            validateModule("""
                fn foo<T>() {
                    x: T = false
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.simpleName shouldBe "Bool"
                    it.targetType.shouldBeInstanceOf<GenericTypeReference>().simpleName shouldBe "T"
                }
        }

        "assignment to generically typed member variable" - {
            "matching types should pass" {
                validateModule("""
                    class Foo<T> {
                        var prop: T = init
                    }
                    fn test<T>(tInst1: T, tInst2: T) {
                        var v = Foo(tInst1)
                        set v.prop = tInst2
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "mismatch should error" {
                validateModule("""
                    class Foo<T> {
                        var x: T = init
                    }
                    fn test<T>(tInst1: T) {
                        var v = Foo(tInst1)
                        set v.x = false
                    }
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        it.sourceType.toString() shouldBe "const Bool"
                        it.targetType.toString() shouldBe "T"
                    }
            }
        }

        "reference to generic type with arguments out of bounds" - {
            "unspecified variance" {
                validateModule("""
                    interface I {}
                    class X<T : I> {}
                    
                    x: X<Any>
                """.trimIndent())
                        .shouldFind<TypeArgumentOutOfBoundsDiagnostic>()
            }

            "out variance" {
                validateModule("""
                    interface I {}
                    class X<out T : I> {}
                    
                    x: X<Any>
                """.trimIndent())
                        .shouldFind<TypeArgumentOutOfBoundsDiagnostic>()
            }

            "in variance" {
                validateModule("""
                    interface I {}
                    class X<in T : I> {}
                    
                    fn test(p: X<Any>) {}
                """.trimIndent())
                    .shouldFind<TypeArgumentOutOfBoundsDiagnostic>()
            }
        }

        "reference to generic type with no type arguments when they are required" {
            validateModule("""
                class X<T> {}
                fn test(p: X) {}
            """.trimIndent())
                .shouldFind<MissingTypeArgumentDiagnostic> {
                    it.parameter.name.value shouldBe "T"
                }
        }

        "reference to generic type with too many type arguments when they are required" {
            validateModule("""
                class X<T> {}
                fn test(p: X<S32, S32, Bool>) {}
            """.trimIndent())
                .shouldFind<SuperfluousTypeArgumentsDiagnostic> {
                    it.nExpected shouldBe 1
                    it.firstSuperfluousArgument.toString() shouldBe "S32"
                }
        }

        "reference to generic type with mismatching parameter variance" {
            validateModule("""
                class X<in T> {}
                fn test(p: X<out Any>) {}
            """.trimIndent())
                .shouldFind<TypeArgumentVarianceMismatchDiagnostic>()

            validateModule("""
                class X<out T> {}
                fn test(p: X<in Any>) {}
            """.trimIndent())
                .shouldFind<TypeArgumentVarianceMismatchDiagnostic>()
        }

        "reference to generic type with superfluous parameter variance" {
            validateModule("""
                class X<in T> {}
                fn test(p: X<in Any>) {}
            """.trimIndent())
                .shouldFind<TypeArgumentVarianceSuperfluousDiagnostic>()
        }

        "reference to generic type with incompatible type argument mutability" - {
            "declaration-site" {
                validateModule("""
                    class A<T : mut Any> {
                        prop: T
                    }
                    fn foo(p: A<const S32>) {}
                """.trimIndent())
                    .shouldFind<TypeArgumentOutOfBoundsDiagnostic> {
                        it.argument.toString() shouldBe "const S32"
                    }
            }

            "use-site" {
                validateModule("""
                    class A<T : mut Any> {
                        prop: T = init
                    }
                    x = A(2)
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        it.sourceType.toString() shouldBe "const S32"
                        it.targetType.toString() shouldBe "mut Any"
                        it.reason shouldBe "cannot assign a const value to a mut reference"
                    }
            }
        }

        "generic validation involving multiple values of different types" {
            /*
            ideally, the compiler should argue this way:
            1. expected return type of invoking the A-constructor is A<S32>,
               hence T = S32 (unnegotiable)
            2. the numeric literal 2 conforms to S32 -> all good
            3. the boolean literal false doesn't conform to S32 -> report an error

            But it currently doesn't. This is tricky to integrate into the type unification process,
            and I've given up last time I tried. So, the compiler currently reasons like so:

            1. expected return type of invoking the A-constructor is A<S32>,
               hence T = S32 (negotiable)
            2. the numeric literal 2 conforms to S32 -> all good
            3. the boolean literal false doesn't conform to S32
               but the type of the literal conforms to the bound of T (which is read Any?),
               so rebind T to the closest common supertype of Bool and S32, which is Any;
               hence now T = Any
            4. The return type of the constructor invocation is (correctly!!) determined to be A<Any>
            5. the return value of the constructor doesn't conform to the expected A<S32> -> report an error ("Any is not a subtype of S32")
             */

            validateModule("""
                class A<T> {
                    propOne: T = init
                    propTwo: T = init
                }
                x: A<S32> = A(2, false)
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const Any"
                    it.targetType.toString() shouldBe "const S32"
                }
        }

        "use-site variance errors" - {
            "in type at class member" {
                validateModule("""
                    class X<in T> {
                        prop: T = init
                    }
                """.trimIndent())
                    .shouldFind<UnsupportedTypeUsageVarianceDiagnostic>()
            }
        }

        "nullability modification on type parameter" - {
            "to nullable" {
                validateModule("""
                    class Test<T : Any> {
                        x: T = init
                        fn getX(self) -> T? = self.x
                    }
                    fn test() {
                        y: String? = Test("abc").getX()
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "parameter typed as a type parameter without explicit nullability takes nullabilit of its use-site bound" {
                validateModule("""
                    intrinsic fn foo<T : Any?>(p: T) -> S32
                    fn test() {
                        foo::<String?>(null)
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }
        }

        "type arguments for a type that doesn't define parameters" {
            validateModule("""
                class C {}
                fn test(p: C<S32, S32>) {}
            """.trimIndent())
                .shouldFind<SuperfluousTypeArgumentsDiagnostic>()
        }

        "unsatisfiable compound constraints" - {
            "failing on supertype constraint" {
                validateModule("""
                    class A {}
                    class B {}
                    interface X<T> {}
                    
                    fn foo<E, F : X<E>>(p1: F, p2: F) {}
                    
                    fn trigger<P1 : X<A>, P2: X<B>>(p1: P1, p2: P2) {
                        foo(p1, p2)
                    }
                """.trimIndent())
                    .shouldFind<UnsatisfiableTypeVariableConstraintsDiagnostic> {
                        it.parameter.name.value shouldBe "E"
                    }
            }

            "failing on subtype constraint, lower bound not satisfiable" {
                validateModule("""
                    class A {}
                    class B {}
                    interface X<T> {}                    
                   
                    fn foo<E>(p1: X<in E>, p2: X<in E>) {}
                    
                    fn trigger(p1: X<A>, p2: X<B>) {
                        foo(p1, p2)
                    }
                """.trimIndent())
                    .shouldFind<UnsatisfiableTypeVariableConstraintsDiagnostic> {
                        it.parameter.name.value shouldBe "E"
                    }
            }

            "failing on subtype constraint, upper bounds incompatible with lower bound" {
                validateModule("""
                    class A {}
                    class B {}
                    
                    interface X<T> {}
                    
                    fn foo<E>(p0: X<out E>, p1: X<in E>) {}
                    
                    fn trigger(p0: X<A>, p1: X<B>) {
                        foo(p0, p1)
                    }
                """.trimIndent())
                    .shouldFind<UnsatisfiableTypeVariableConstraintsDiagnostic> {
                        it.parameter.name.value shouldBe "E"
                    }
            }

            "failing on exact constraint, not compatible with default upper bound" {
                validateModule("""
                    class A {}
                    class B {}
                    interface X<T : A> {}
                    
                    fn trigger(p: X<B>) {}
                """.trimIndent())
                    .shouldFind<TypeArgumentOutOfBoundsDiagnostic>()
            }
        }
    }

    "array literal" - {
        "with no elements is Array<Any>" {
            validateModule("""
                x = []
                y: Array<String> = x
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read Any"
                    it.targetType.toString() shouldBe "read String"
                }
        }

        "infers array type from elements" - {
            "all the same" {
                validateModule("""
                    x = [1, 2, 3]
                    y: Array<String> = x
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        it.sourceType.toString() shouldBe "const S32"
                        it.targetType.toString() shouldBe "read String"
                    }
            }

            "different types" {
                validateModule("""
                    x = [1, 2, 4, 5]
                    y: Array<String> = x
                """.trimIndent())
                    .shouldFind<ValueNotAssignableDiagnostic> {
                        it.sourceType.toString() shouldBe "const S32"
                        it.targetType.toString() shouldBe "read String"
                    }
            }
        }

        "uses element type from expected return" {
            validateModule("""
                x: Array<S32> = [1, 2, 3, 4]
                y: Array<String> = x
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const S32"
                    it.targetType.toString() shouldBe "read String"
                }
        }

        "validates expected return element type against elements" {
            validateModule("""
                x: Array<S32> = [1, 2, 3, "4"]
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const String"
                    it.targetType.toString() shouldBe "const S32"
                }
        }
    }

    "union types" - {
        "superfluous components" {
            validateModule("""
                interface I {}
                interface S : I {}
                
                fn trigger(p: I & S) {}
            """.trimIndent())
                .shouldFind<SimplifiableIntersectionTypeDiagnostic> {
                    it.complicatedType.toString() shouldBe "I & S"
                    it.simplerVersion.toString() shouldBe "read testmodule.S"
                }

            validateModule("""
                fn trigger(p: S32 & read Any) {}
            """.trimIndent())
                .shouldFind<SimplifiableIntersectionTypeDiagnostic> {
                    it.complicatedType.toString() shouldBe "S32 & read Any"
                    it.simplerVersion.toString() shouldBe "const S32"
                }

            validateModule("""
                fn trigger(p: read Any & S32) {}
            """.trimIndent())
                .shouldFind<SimplifiableIntersectionTypeDiagnostic> {
                    it.complicatedType.toString() shouldBe "read Any & S32"
                    it.simplerVersion.toString() shouldBe "const S32"
                }

            validateModule("""
                interface I {}
                
                fn trigger(p: read I & mut Any) {}
            """.trimIndent())
                .shouldFind< SimplifiableIntersectionTypeDiagnostic> {
                    it.complicatedType.toString() shouldBe "read I & mut Any"
                    it.simplerVersion.toString() shouldBe "mut testmodule.I"
                }
        }
    }

    "regressions" - {
        "type argument unification with nullability" {
            validateModule("""
                class C<T> {}
                fn test<X>() {
                    v: C<X?> = C::<X?>()
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }
})