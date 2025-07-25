package compiler.compiler.negative

import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundVariable
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.diagnostic.ElementNotAccessibleDiagnostic
import compiler.diagnostic.HiddenTypeExposedDiagnostic
import compiler.diagnostic.MissingModuleDependencyDiagnostic
import compiler.diagnostic.OverrideRestrictsVisibilityDiagnostic
import compiler.diagnostic.ShadowedVisibilityDiagnostic
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf
import io.kotest.matchers.types.shouldBeInstanceOf

class VisibilityTests : FreeSpec({
    "global variables" - {
        "access is verified on import" - {
            "explicit import" {
                validateModules(
                    IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    module x = 3
                """.trimIndent()),
                    IntegrationTestModule.of("module_B", """
                    package module_B
                    
                    import module_A.x 
                    
                    fn dummy() {}
                """.trimIndent())
                )
                    .shouldFind<ElementNotAccessibleDiagnostic> {
                        it.element should beInstanceOf<BoundVariable>()
                    }
            }
        }

        "access is verified on use with wildcard import" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    module x = 3
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    
                    import module_A.* 
                    
                    fn dummy() = x
                """.trimIndent())
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element should beInstanceOf<BoundVariable>()
                }
        }
    }

    "member variables" - {
        "access is verified on read" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    class Foo {
                        module x = 3
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fn test() -> S32 {
                        v = Foo()
                        return v.x
                    }
                """.trimIndent()),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element should beInstanceOf<BoundBaseTypeMemberVariable>()
                }
        }

        "access is verified on write" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    export class Foo {
                        module var x = 3
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fn test() {
                        var v = Foo()
                        set v.x = 5
                    }
                """.trimIndent(),
                    uses = setOf(CanonicalElementName.Package(listOf("module_A")))),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    val element = it.element
                    element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>()
                    element.name shouldBe "x"
                }
        }

        "explicit overexposure export over default module" {
            validateModule("""
                class Foo {
                    export bla: S32 = init
                }
            """.trimIndent())
                .shouldFind<ShadowedVisibilityDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }

        "explicit overexposure export over private" {
            validateModule("""
                private class Foo {
                    export bla: S32 = init
                }
            """.trimIndent())
                .shouldFind<ShadowedVisibilityDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }

        "explicit overexposure explicit module over private" {
            validateModule("""
                private class Foo {
                    module bla: S32 = init
                }
            """.trimIndent())
                .shouldFind<ShadowedVisibilityDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }
    }

    "member functions" - {
        "access is verified on invocation" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    class Foo {
                        export constructor {}
                        module fn foo(self) {}
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fn test() {
                        v = Foo()
                        v.foo()
                    }
                """.trimIndent()),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundDeclaredFunction>().canonicalName.toString() shouldBe "module_A.Foo::foo"
                }
        }
    }

    "constructors" - {
        "access is verified on invocation" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    class Foo {
                        module constructor {}
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fn test() {
                        v = Foo()
                    }
                """.trimIndent()),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundClassConstructor>()
                }
        }
    }

    "top level functions" - {
        "access is verified on import" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    module fn foo() {}
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.foo
                    fn dummy() {}
                """.trimIndent()),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundDeclaredFunction>()
                }
        }

        "access is verified on invocation" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    module fn foo() {}
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.*
                    fn test() {
                        foo()
                    }
                """.trimIndent()),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element.shouldBeInstanceOf<BoundDeclaredFunction>()
                }
        }
    }

    "base types" - {
        "access is verified on import" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    module class Foo {}
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fn dummy() {}
                """.trimIndent()),
            )
                .shouldFind<ElementNotAccessibleDiagnostic> {
                    it.element should beInstanceOf<BoundBaseType>()
                }
        }

        "access is verified on use" - {
            "simple type reference" {
                validateModules(
                    IntegrationTestModule.of("module_A", """
                        package module_A
                        
                        module class Foo {}
                    """.trimIndent()),
                    IntegrationTestModule.of("module_B", """
                        package module_B
                        import module_A.*
                        fn test() -> Foo {}
                    """.trimIndent()),
                )
                    .shouldFind<ElementNotAccessibleDiagnostic> {
                        it.element should beInstanceOf<BoundBaseType>()
                    }
            }

            "type parameter" {
                validateModules(
                    IntegrationTestModule.of("module_A", """
                        package module_A
                        
                        module class Foo {}
                    """.trimIndent()),
                    IntegrationTestModule.of("module_B", """
                        package module_B
                        import module_A.*
                        fn test<T : Foo>() {}
                    """.trimIndent()),
                )
                    .shouldFind<ElementNotAccessibleDiagnostic> {
                        it.element should beInstanceOf<BoundBaseType>()
                    }
            }

            "type argument" {
                validateModules(
                    IntegrationTestModule.of("module_A", """
                        package module_A
                        
                        module class Foo {}
                    """.trimIndent()),
                    IntegrationTestModule.of("module_B", """
                        package module_B
                        import module_A.*
                        class Bar<T> {}
                        intrinsic fn test() -> Bar<Foo>
                    """.trimIndent()),
                )
                    .shouldFind<ElementNotAccessibleDiagnostic> {
                        it.element should beInstanceOf<BoundBaseType>()
                    }
            }
        }
    }

    "cross module" - {
        "requires explicit dependency" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    import module_B.foo
                    
                    export fn test() {
                        foo()
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    
                    export fn foo() {}
                """.trimIndent())
            )
                .shouldFind<MissingModuleDependencyDiagnostic> {
                    it.moduleOfAccess.toString() shouldBe "module_A"
                    it.moduleOfAccessedElement.toString() shouldBe "module_B"
                }
        }
    }

    "voldemort types" - {
        "function parameter" {
            validateModule("""
                private class Foo {}
                module fn test(p: Foo) {}
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "function parameter type argument" {
            validateModule("""
                export class A<T> {}
                private class B {}
                export fn test(p: A<B>) {}
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "B"
                }
        }

        "function return type" {
            validateModule("""
                private class Foo {}
                module fn test() -> Foo {}
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "function return type argument" {
            validateModule("""
                export class A<T> {}
                private class B {}
                intrinsic export fn test() -> A<B>
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "B"
                }
        }

        "function type parameter bound" {
            validateModule("""
                private class Foo {}
                module fn test<T : Foo>() {}
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "class type parameter bound" {
            validateModule("""
                private class Foo {}
                module class Bar<T : Foo> {}
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "class member variable type" - {
            validateModule("""
                private class Foo {}
                module class Bar {
                    module x: Foo? = null
                }
            """.trimIndent())
                .shouldFind<HiddenTypeExposedDiagnostic> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "receiver parameter exception" - {
            "applies to member functions" {
                validateModule("""
                    export interface I {
                        fn foo(self: mut _)
                    }
                    class C : I {
                        override fn foo(self: mut C) {}
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "does not apply to toplevel functions" {
                validateModule("""
                    private class C {}
                    export fn test(self: C) {}
                """.trimIndent())
                    .shouldFind<HiddenTypeExposedDiagnostic>()
            }
        }
    }

    "voldemort overrides" {
        validateModule("""
            export interface I {
                export fn foo(self)
            }
            export class C : I {
                override fn foo(self) {}
            }
        """.trimIndent())
            .shouldFind<OverrideRestrictsVisibilityDiagnostic>()
    }
})