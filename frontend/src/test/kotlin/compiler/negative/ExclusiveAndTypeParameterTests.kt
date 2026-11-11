package compiler.compiler.negative

import compiler.diagnostic.ExclusiveTypeArgumentDiagnostic
import compiler.diagnostic.ExclusiveTypeParameterBoundDiagnostic
import compiler.diagnostic.SimultaneousIncompatibleBorrowsDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.VariableUsedAfterLifetimeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

/**
 * `exclusive` is a promise about one reference, upheld by tracking the lifetime of the variable holding it. Generic
 * code copies values of type `T` freely, so a type parameter must never be bound to an `exclusive` type.
 */
class ExclusiveAndTypeParameterTests : FreeSpec({
    "inference never binds a type parameter to an exclusive type" - {
        "an exclusive argument decays to mut" {
            validateModule("""
                class Foo {}
                fn g<T>(x: T) -> T = x
                fn test() {
                    y: exclusive Foo = g(Foo())
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "mut testmodule.Foo"
                }
        }

        "the decayed value is mut" {
            validateModule("""
                class Foo {}
                fn g<T>(x: T) -> T = x
                fn test() {
                    y: mut Foo = g(Foo())
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "passing an exclusive variable for a parameter of type T ends its lifetime" {
            validateModule("""
                class Foo {}
                fn g<T>(x: T) -> T = x
                fn f(x: exclusive Foo) -> exclusive Foo {
                    y = g(x)
                    return x
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "x"
                }
        }

        "the expected type decides the mutability, where there is one" - {
            "const" {
                validateModule("""
                    class Foo {}
                    class Box<T> {
                        var value: T = init
                    }
                    fn test() {
                        b: mut Box<const Foo> = Box(Foo())
                    }
                """.trimIndent()) should haveNoDiagnostics()
            }

            "mut" {
                validateModule("""
                    class Foo {}
                    class Box<T> {
                        var value: T = init
                    }
                    fn test() {
                        b: mut Box<mut Foo> = Box(Foo())
                    }
                """.trimIndent()) should haveNoDiagnostics()
            }

            "read" {
                validateModule("""
                    class Foo {}
                    class Box<T> {
                        var value: T = init
                    }
                    fn test() {
                        b: mut Box<read Foo> = Box(Foo())
                    }
                """.trimIndent()) should haveNoDiagnostics()
            }
        }

        "other arguments decide the mutability, where there are some" {
            validateModule("""
                class Foo {}
                fn pick<T>(a: T, b: T) -> T = a
                fn test(c: const Foo) {
                    x: const Foo = pick(Foo(), c)
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "exclusive cannot be written where a type parameter would be bound to it" - {
        "type argument of a function call" {
            validateModule("""
                class Foo {}
                fn test() {
                    arr = Array.new::<exclusive Foo>(20, Foo())
                }
            """.trimIndent())
                .shouldFind<ExclusiveTypeArgumentDiagnostic>()
        }

        "type argument of a type" {
            validateModule("""
                class Foo {}
                class Box<T> {
                    var value: T = init
                }
                fn test(b: Box<exclusive Foo>) {}
            """.trimIndent())
                .shouldFind<ExclusiveTypeArgumentDiagnostic>()
        }

        "type argument of a type, with variance" {
            validateModule("""
                class Foo {}
                class Box<T> {
                    var value: T = init
                }
                fn test(b: Box<out exclusive Foo>) {}
            """.trimIndent())
                .shouldFind<ExclusiveTypeArgumentDiagnostic>()
        }

        "type argument that is a type parameter" {
            validateModule("""
                class Box<T> {
                    var value: T = init
                }
                fn test<T>(b: Box<exclusive T>) {}
            """.trimIndent())
                .shouldFind<ExclusiveTypeArgumentDiagnostic>()
        }

        "bound of a type parameter" {
            validateModule("""
                class Foo {}
                fn test<T : exclusive Foo>(x: T) {}
            """.trimIndent())
                .shouldFind<ExclusiveTypeParameterBoundDiagnostic>()
        }

        "an exclusive type with type arguments is fine" {
            validateModule("""
                class Foo {}
                fn test() -> exclusive Array<mut Foo> {
                    return Array.new::<mut Foo>(20, Foo())
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "exclusive on a use of a type parameter" - {
        "is still an exclusive value of the type argument" {
            validateModule("""
                class Foo {}
                fn pass<T>(x: exclusive T) -> exclusive T = x
                fn test() {
                    a: exclusive Foo = pass::<read Foo>(Foo())
                    b: exclusive Foo = pass(Foo())
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "capturing it as a T ends its lifetime" {
            validateModule("""
                class Box<T> {
                    var value: T = init
                }
                fn f<T>(x: exclusive T, b: mut Box<T>) -> exclusive T {
                    set b.value = x
                    return x
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "x"
                }
        }

        "passing it for a parameter of type T ends its lifetime" {
            validateModule("""
                fn sink<T>(x: T) {}
                fn f<T>(x: exclusive T) -> exclusive T {
                    sink(x)
                    return x
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "x"
                }
        }

        "capturing it as a read T ends its lifetime, as that is a mut reference for a mut type argument" {
            validateModule("""
                class Box<T> {
                    var value: T = init
                }
                fn f<T>(x: exclusive T, b: mut Box<read T>) -> exclusive T {
                    set b.value = x
                    return x
                }
            """.trimIndent())
                .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                    it.variable.name.value shouldBe "x"
                }
        }

        "borrowing it as a T cannot go with a mut borrow, as that is a const reference for a const type argument" {
            validateModule("""
                fn two<T>(borrow a: T, borrow b: mut Any?) {}
                fn f<T>(x: exclusive T) {
                    two::<T>(x, x)
                }
            """.trimIndent())
                .shouldFind<SimultaneousIncompatibleBorrowsDiagnostic>()
        }

        "capturing it as a read reference does not end its lifetime" {
            validateModule("""
                class Box<T> {
                    var value: T = init
                }
                fn f<T>(x: exclusive T, b: mut Box<read Any?>) -> exclusive T {
                    set b.value = x
                    return x
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }
})
