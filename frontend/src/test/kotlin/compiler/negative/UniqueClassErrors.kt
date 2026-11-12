package compiler.compiler.negative

import compiler.diagnostic.ConstTokenDiagnostic
import compiler.diagnostic.ElementNotAccessibleDiagnostic
import compiler.diagnostic.IllegalMainSignatureDiagnostic
import compiler.diagnostic.IllegalUniqueDeclarationDiagnostic
import compiler.diagnostic.UniqueClassConstructorInvocationDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.string.shouldContain

/**
 * A `unique class` is a token class with at most one instance per process. The compiler adds the static function
 * `take` that hands the instance out once; the constructor cannot be invoked in any other way.
 */
class UniqueClassErrors : FreeSpec({
    "take hands out the instance, given the root as mut" {
        validateModule("""
            import emerge.platform.World
            unique class Usb {
                var resets: S32 = 0
                fn reset(self: mut _) {
                    set self.resets = self.resets + 1
                }
            }
            fn test(world: mut World) {
                usb: mut Usb = Usb.take(world)!!
                usb.reset()
            }
        """.trimIndent()) should haveNoDiagnostics()
    }

    "take forwards the parameters of the constructor" {
        validateModule("""
            import emerge.platform.World
            unique class Usb {
                logLevel: S32 = init
                name: String = init
            }
            fn test(world: mut World) -> own Usb? {
                return Usb.take(world, 3, "main")
            }
        """.trimIndent()) should haveNoDiagnostics()
    }

    "take needs the root as mut" {
        validateModule("""
            import emerge.platform.World
            unique class Usb {}
            fn test(world: read World) {
                usb = Usb.take(world)
            }
        """.trimIndent())
            .shouldFind<ValueNotAssignableDiagnostic>()
    }

    "the constructor cannot be invoked" - {
        "from other code" {
            validateModule("""
                unique class Usb {}
                fn test() {
                    usb = Usb()
                }
            """.trimIndent())
                .shouldFind<UniqueClassConstructorInvocationDiagnostic> {
                    it.message shouldContain "Usb.take"
                }
        }

        "from inside the class" {
            validateModule("""
                unique class Usb {
                    fn another() -> own Usb = Usb()
                }
            """.trimIndent())
                .shouldFind<UniqueClassConstructorInvocationDiagnostic>()
        }
    }

    "take has the visibility of the constructor" {
        validateModules(
            IntegrationTestModule.of("lib", """
                package lib
                
                import emerge.platform.World

                export unique class Usb {
                    private constructor {}
                }
                export fn open(world: mut World) -> own Usb? = Usb.take(world)
            """.trimIndent()),
            IntegrationTestModule.of("app", """
                package app
                
                import emerge.platform.World
                import lib.Usb
                import lib.open

                fn viaLibrary(world: mut World) -> own Usb? = open(world)
                fn direct(world: mut World) -> own Usb? = Usb.take(world)
            """.trimIndent(), uses = setOf(io.github.tmarsteel.emerge.common.CanonicalElementName.Package(listOf("lib")))),
        )
            .shouldFind<ElementNotAccessibleDiagnostic>()
    }

    "a unique class is a token class" - {
        "it cannot be forgotten" {
            validateModule("""
                import emerge.platform.World
                unique class Usb {}
                fn test(world: mut World) {
                    n: read NonToken? = Usb.take(world)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "it cannot be const" {
            validateModule("""
                unique class Usb {}
                fn test(usb: const Usb) {}
            """.trimIndent())
                .shouldFind<ConstTokenDiagnostic>()
        }

        "it can implement a token interface" {
            validateModule("""
                token interface Stream {}
                unique class StandardOut : Stream {}
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "declaration" - {
        "an interface cannot be unique" {
            validateModule("""
                unique interface Usb {}
            """.trimIndent())
                .shouldFind<IllegalUniqueDeclarationDiagnostic>()
        }

        "a unique class cannot have type parameters" {
            validateModule("""
                unique class Registry<T> {}
            """.trimIndent())
                .shouldFind<IllegalUniqueDeclarationDiagnostic>()
        }

        "unique is still usable as a name where it is delimited" {
            validateModule("""
                fn test(`unique`: S32) -> S32 = `unique`
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "the main function" - {
        "takes no parameter" {
            validateModule("""
                fn main() {}
            """.trimIndent()) should haveNoDiagnostics()
        }

        "or the root, with a mutability of its choice" {
            validateModule("""
                import emerge.platform.World
                fn main(world: mut World) {}
            """.trimIndent()) should haveNoDiagnostics()

            validateModule("""
                import emerge.platform.World
                fn main(world: read World) {}
            """.trimIndent()) should haveNoDiagnostics()
        }

        "takes nothing else" {
            validateModule("""
                fn main(args: Array<String>) {}
            """.trimIndent())
                .shouldFind<IllegalMainSignatureDiagnostic>()

            validateModule("""
                import emerge.platform.World
                fn main(world: mut World, n: S32) {}
            """.trimIndent())
                .shouldFind<IllegalMainSignatureDiagnostic>()

            validateModule("""
                import emerge.platform.World
                fn main(world: mut World?) {}
            """.trimIndent())
                .shouldFind<IllegalMainSignatureDiagnostic>()
        }
    }
})
