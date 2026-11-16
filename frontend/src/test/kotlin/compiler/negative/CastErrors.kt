package compiler.compiler.negative

import compiler.diagnostic.ForbiddenCastDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import io.kotest.core.spec.style.FreeSpec

/**
 * The runtime checks casts against base types, type arguments and nullability, but not against mutability. These are
 * the rules that keep a cast from claiming a mutability nothing proves.
 */
class CastErrors : FreeSpec({
    val declarations = """
        interface Foo {}
        class Bar : Foo {}
    """.trimIndent()

    "mutability of the value" - {
        "can be kept" {
            validateModule("""
                $declarations
                fn test(x: mut Any) -> mut Foo = x as mut Foo
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "can be weakened" {
            validateModule("""
                $declarations
                fn test(x: mut Any) -> read Foo = x as read Foo
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "cannot be strengthened" {
            validateModule("""
                $declarations
                fn test(x: read Any) -> mut Foo = x as mut Foo
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()

            validateModule("""
                $declarations
                fn test(x: read Any) -> const Foo = x as const Foo
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "own is never the target" {
            validateModule("""
                $declarations
                fn test(x: mut Any) -> mut Foo = x as own Foo
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "a safe cast follows the same rules" {
            validateModule("""
                $declarations
                fn test(x: read Any) -> mut Foo? = x as? mut Foo
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "types that are const by themselves need no proof" {
            validateModule("""
                fn test(x: read Any) -> const String = x as String
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "mutability in type arguments, where the type of the value says nothing about them" - {
        "an invariant type argument reads as out read" {
            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<out Foo> = x as Array<Foo>
            """.trimIndent())
                .shouldHaveNoDiagnostics()

            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<Foo> = x as Array<Foo>
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }

        "an invariant type argument that is const by itself stays invariant" {
            validateModule("""
                fn test(x: read Any) -> Array<String> = x as Array<String>
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "mut and const are not proven" {
            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<out mut Foo> = x as Array<out mut Foo>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()

            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<out Foo> = x as Array<const Foo>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "nested type arguments" {
            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<out Array<out Foo>> = x as Array<Array<Foo>>
            """.trimIndent())
                .shouldHaveNoDiagnostics()

            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<out Array<out Foo>> = x as Array<Array<mut Foo>>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "in-variant type arguments cannot be the target" {
            validateModule("""
                $declarations
                fn test(x: read Any) -> Array<in Bar> = x as Array<in Bar>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "wildcards are fine" {
            validateModule("""
                fn test(x: read Any) -> Array<*> = x as Array<*>
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "mutability in type arguments that the type of the value proves" - {
        "an out argument proves mut" {
            validateModule("""
                $declarations
                fn test(x: Array<out mut Foo>) -> Array<mut Bar> = x as Array<mut Bar>
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "an out argument proves const" {
            validateModule("""
                $declarations
                fn test(x: Array<out const Foo>) -> Array<const Bar> = x as Array<const Bar>
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "an out read argument proves nothing" {
            validateModule("""
                $declarations
                fn test(x: Array<out Foo>) -> Array<out Bar> = x as Array<mut Bar>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()

            validateModule("""
                $declarations
                fn test(x: Array<out Foo>) -> Array<out Bar> = x as Array<Bar>
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "what is proven mut cannot become const" {
            validateModule("""
                $declarations
                fn test(x: Array<out mut Foo>) -> Array<out Bar> = x as Array<const Bar>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }

        "what is proven can be weakened in an out argument" {
            validateModule("""
                $declarations
                fn test(x: Array<out mut Foo>) -> Array<out Bar> = x as Array<out Bar>
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "the supertype of the value proves nothing about the type arguments of a subtype" {
            validateModule("""
                import emerge.core.range.Iterable
                $declarations
                fn test(x: Iterable<mut Foo>) -> Array<out Foo> = x as Array<mut Foo>
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }
    }
})
