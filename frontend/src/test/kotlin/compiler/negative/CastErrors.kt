package compiler.compiler.negative

import compiler.diagnostic.ForbiddenCastDiagnostic
import io.kotest.core.spec.style.FreeSpec

/**
 * An object doesn't know the mutability of the references to it, so a cast cannot make a reference more than it is.
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

    "mutability in type arguments is left to the check at runtime, objects know their type arguments" {
        validateModule("""
            $declarations
            fn a(x: read Any) -> Array<mut Foo> = x as Array<mut Foo>
            fn b(x: read Any) -> Array<Foo> = x as Array<Foo>
            fn c(x: read Any) -> Array<in Bar> = x as Array<in Bar>
            fn d(x: Array<out Foo>) -> Array<const Bar> = x as Array<const Bar>
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "a type parameter as the target" - {
        "is left to the check at runtime, where the mutability of the type argument is known" {
            validateModule("""
                fn castTo<T>(x: read Any) -> T = x as T
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "cannot be of a stronger mutability than the value, where its bound says so already" {
            validateModule("""
                $declarations
                fn castTo<T : mut Foo>(x: read Any) -> T = x as T
            """.trimIndent())
                .shouldFind<ForbiddenCastDiagnostic>()
        }
    }
})
