package compiler.compiler.negative

import compiler.diagnostic.OwnTypeArgumentDiagnostic
import compiler.diagnostic.OwnTypeParameterBoundDiagnostic
import compiler.diagnostic.SimultaneousIncompatibleBorrowsDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.VariableUsedAfterLifetimeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

/**
 * `own` is a promise about one reference, upheld by tracking the lifetime of the variable holding it. Generic
 * code copies values of type `T` freely, so a type parameter must never be bound to an `own` type.
 */
class OwnAndTypeParameterTests : FreeSpec({
    "inference never binds a type parameter to an own type" - {
        "an own argument decays to mut" {
            validateModule("""
                class Foo {}
                fn g<T>(x: T) -> T = x
                fn test() {
                    y: own Foo = g(Foo())
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

        "passing an own variable for a parameter of type T ends its lifetime" {
            validateModule("""
                class Foo {}
                fn g<T>(x: T) -> T = x
                fn f(x: own Foo) -> own Foo {
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

    "own cannot be written where a type parameter would be bound to it" - {
        "type argument of a function call" {
            validateModule("""
                class Foo {}
                fn test() {
                    arr = Array.new::<own Foo>(20, Foo())
                }
            """.trimIndent())
                .shouldFind<OwnTypeArgumentDiagnostic>()
        }

        "type argument of a type" {
            validateModule("""
                class Foo {}
                class Box<T> {
                    var value: T = init
                }
                fn test(b: Box<own Foo>) {}
            """.trimIndent())
                .shouldFind<OwnTypeArgumentDiagnostic>()
        }

        "type argument of a type, with variance" {
            validateModule("""
                class Foo {}
                class Box<T> {
                    var value: T = init
                }
                fn test(b: Box<out own Foo>) {}
            """.trimIndent())
                .shouldFind<OwnTypeArgumentDiagnostic>()
        }

        "type argument that is a type parameter" {
            validateModule("""
                class Box<T> {
                    var value: T = init
                }
                fn test<T>(b: Box<own T>) {}
            """.trimIndent())
                .shouldFind<OwnTypeArgumentDiagnostic>()
        }

        "bound of a type parameter" {
            validateModule("""
                class Foo {}
                fn test<T : own Foo>(x: T) {}
            """.trimIndent())
                .shouldFind<OwnTypeParameterBoundDiagnostic>()
        }

        "an own type with type arguments is fine" {
            validateModule("""
                class Foo {}
                fn test() -> own Array<mut Foo> {
                    return Array.new::<mut Foo>(20, Foo())
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "own on a use of a type parameter" - {
        "is still an own value of the type argument" {
            validateModule("""
                class Foo {}
                fn pass<T>(x: own T) -> own T = x
                fn test() {
                    a: own Foo = pass::<read Foo>(Foo())
                    b: own Foo = pass(Foo())
                }
            """.trimIndent()) should haveNoDiagnostics()
        }

        "capturing it as a T ends its lifetime" {
            validateModule("""
                class Box<T> {
                    var value: T = init
                }
                fn f<T>(x: own T, b: mut Box<T>) -> own T {
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
                fn f<T>(x: own T) -> own T {
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
                fn f<T>(x: own T, b: mut Box<read T>) -> own T {
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
                fn f<T>(x: own T) {
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
                fn f<T>(x: own T, b: mut Box<read Any?>) -> own T {
                    set b.value = x
                    return x
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }
})
