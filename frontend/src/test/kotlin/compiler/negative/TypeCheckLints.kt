package compiler.compiler.negative

import compiler.diagnostic.ForbiddenCastDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.TypeCheckAlwaysSucceedsDiagnostic
import compiler.diagnostic.TypeCheckKind
import compiler.diagnostic.TypeCheckNeverSucceedsDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

/**
 * Where the static type of the value tells the result of an `is` or `as` already, that is reported.
 */
class TypeCheckLints : FreeSpec({
    val declarations = """
        interface Foo {}
        interface Other {}
        class Bar : Foo {}
        class Baz {}
        class Box<E> {}
        interface Seq<E> {}
        class Nest<E> : Seq<Box<E>> {}
    """.trimIndent()

    "always succeeds" - {
        "is" {
            validateModule("""
                $declarations
                fn test(x: Bar) -> Bool = x is Foo
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic> {
                    it.kind shouldBe TypeCheckKind.INSTANCE_OF
                }
        }

        "as" {
            validateModule("""
                $declarations
                fn test(x: Bar) -> Foo = x as Foo
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic> {
                    it.kind shouldBe TypeCheckKind.CAST
                }
        }

        "as?" {
            validateModule("""
                $declarations
                fn test(x: Bar) -> Foo? = x as? Foo
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic> {
                    it.kind shouldBe TypeCheckKind.SAFE_CAST
                }
        }

        "to the very type of the value" {
            validateModule("""
                $declarations
                fn test(x: Box<Bar>) -> Bool = x is Box<Bar>
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic>()
        }

        "weakening the mutability" {
            validateModule("""
                $declarations
                fn test(x: mut Bar) -> Bool = x is read Foo
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic>()
        }

        "to the bound of a type parameter" {
            validateModule("""
                $declarations
                fn test<T : Foo>(x: T) -> Bool = x is Foo
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic>()
        }

        "not for a nullable value and a non-nullable type" {
            validateModule("""
                $declarations
                fn test(x: Bar?) -> Bool = x is Bar
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not for a numeric literal, where the cast says the type" {
            validateModule("""
                fn test() -> U16 = 3 as U16
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not for a cast of an intersection to one of its components, which tells their members apart" {
            validateModule("""
                $declarations
                fn test(x: Foo & Other) -> Foo = x as Foo
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "such a cast doesn't throw" {
            validateModule("""
                $declarations
                nothrow fn test(x: Bar) -> Foo = x as Foo
            """.trimIndent())
                .shouldFind<TypeCheckAlwaysSucceedsDiagnostic>()
                .shouldNotFind<NothrowViolationDiagnostic>()
        }
    }

    "never succeeds" - {
        "is, two classes" {
            validateModule("""
                $declarations
                fn test(x: Bar) -> Bool = x is Baz
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic> {
                    it.kind shouldBe TypeCheckKind.INSTANCE_OF
                }
        }

        "as, two classes" {
            validateModule("""
                $declarations
                fn test(x: Bar) -> Baz = x as Baz
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic> {
                    it.kind shouldBe TypeCheckKind.CAST
                }
        }

        "as?, two classes" {
            validateModule("""
                $declarations
                fn test(x: Bar) -> Baz? = x as? Baz
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic> {
                    it.kind shouldBe TypeCheckKind.SAFE_CAST
                }
        }

        "a class to an interface it doesn't implement" {
            validateModule("""
                $declarations
                fn test(x: Baz) -> Bool = x is Foo
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic>()
        }

        "an interface to a class that doesn't implement it" {
            validateModule("""
                $declarations
                fn test(x: Foo) -> Bool = x is Baz
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic>()
        }

        "not for two interfaces, a class may implement both" {
            validateModule("""
                $declarations
                fn test(x: Foo) -> Bool = x is Other
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not for an interface and a class that implements it" {
            validateModule("""
                $declarations
                fn test(x: Foo) -> Bool = x is Bar
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not where null is a value of both types" {
            validateModule("""
                $declarations
                fn test(x: Bar?) -> Bool = x is Baz?
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a nullable value of another class" {
            validateModule("""
                $declarations
                fn test(x: Bar?) -> Bool = x is Baz
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic>()
        }

        "by the bound of a type parameter" {
            validateModule("""
                $declarations
                fn a<T : Bar>(x: T) -> Bool = x is Baz
                fn b<T : Bar>(x: Baz) -> Bool = x is T
            """.trimIndent())
                .shouldFind<TypeCheckNeverSucceedsDiagnostic>(allowMultiple = true)
                .second.count { it is TypeCheckNeverSucceedsDiagnostic } shouldBe 2
        }

        "type arguments" - {
            "exact ones that differ" {
                validateModule("""
                    $declarations
                    fn test(x: Box<Bar>) -> Bool = x is Box<Baz>
                """.trimIndent())
                    .shouldFind<TypeCheckNeverSucceedsDiagnostic>()
            }

            "exact ones that differ in mutability" {
                validateModule("""
                    $declarations
                    fn test(x: Box<mut Bar>) -> Bool = x is Box<read Bar>
                """.trimIndent())
                    .shouldFind<TypeCheckNeverSucceedsDiagnostic>()
            }

            "an exact one outside of a variant one" {
                validateModule("""
                    $declarations
                    fn a(x: Box<out Foo>) -> Bool = x is Box<Baz>
                    fn b(x: Box<Baz>) -> Bool = x is Box<out Foo>
                    fn c(x: Box<in Bar>) -> Bool = x is Box<Baz>
                """.trimIndent())
                    .shouldFind<TypeCheckNeverSucceedsDiagnostic>(allowMultiple = true)
                    .second.count { it is TypeCheckNeverSucceedsDiagnostic } shouldBe 3
            }

            "not where a variant one can be met" {
                validateModule("""
                    $declarations
                    fn a(x: Box<out Foo>) -> Bool = x is Box<Bar>
                    fn b(x: Box<out Foo>) -> Bool = x is Box<out Baz>
                    fn c(x: Box<in Bar>) -> Bool = x is Box<Foo>
                    fn d(x: Box<in Bar>) -> Bool = x is Box<in Baz>
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "not where a type parameter is involved" {
                validateModule("""
                    $declarations
                    fn test<T>(x: Box<T>) -> Bool = x is Box<Baz>
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "through a supertype" {
                validateModule("""
                    $declarations
                    fn a(x: Seq<Box<Bar>>) -> Bool = x is Nest<Baz>
                    fn b(x: Nest<Baz>) -> Bool = x is Seq<Box<Bar>>
                """.trimIndent())
                    .shouldFind<TypeCheckNeverSucceedsDiagnostic>(allowMultiple = true)
                    .second.count { it is TypeCheckNeverSucceedsDiagnostic } shouldBe 2
            }

            "not through a supertype where it fits" {
                validateModule("""
                    $declarations
                    fn a(x: Seq<Box<Bar>>) -> Bool = x is Nest<Bar>
                    fn b(x: Seq<out Any>) -> Bool = x is Nest<Baz>
                    fn c(x: Seq<Box<Bar>>) -> Bool = x is Nest<out Foo>
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }
        }

        "mutability" - {
            "is, a read reference to an object of a class with state is never mut" {
                validateModule("""
                    $declarations
                    fn a(x: read Bar) -> Bool = x is mut Bar
                    fn b(x: read Foo) -> Bool = x is mut Bar
                    fn c(x: read Bar) -> Bool = x is mut Foo
                    fn d(x: read Bar) -> Bool = x is const Bar
                    fn e(x: mut Bar) -> Bool = x is const Foo
                """.trimIndent())
                    .shouldFind<TypeCheckNeverSucceedsDiagnostic>(allowMultiple = true)
                    .second.count { it is TypeCheckNeverSucceedsDiagnostic } shouldBe 5
            }

            "is, not where the object may be of a class that is const by itself, which is a value of any mutability" {
                validateModule("""
                    $declarations
                    fn a(x: read Any) -> Bool = x is mut Foo
                    fn b(x: read Any) -> Bool = x is mut Any
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "is, not where the mutability of the reference is that of a type argument" {
                validateModule("""
                    $declarations
                    fn test<T : Foo>(x: T) -> Bool = x is mut Bar
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "as, the error is the only diagnostic" {
                validateModule("""
                    $declarations
                    fn test(x: read Bar) -> mut Bar = x as mut Bar
                """.trimIndent())
                    .shouldFind<ForbiddenCastDiagnostic>()
                    .shouldNotFind<TypeCheckNeverSucceedsDiagnostic>()
            }
        }
    }
})
