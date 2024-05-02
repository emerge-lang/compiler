package compiler.compiler.negative

import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundVariable
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.reportings.ElementNotAccessibleReporting
import compiler.reportings.HiddenTypeExposedReporting
import compiler.reportings.ShadowedVisibilityReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf
import io.kotest.matchers.types.shouldBeInstanceOf

class VisibilityTests : FreeSpec({
    "global variables" - {
        "access is verified on import" {
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
                .shouldReport<ElementNotAccessibleReporting> {
                    it.element should beInstanceOf<BoundVariable>()
                }
        }

        "access is verified on use" {
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
                .shouldReport<ElementNotAccessibleReporting> {
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
                .shouldReport<ElementNotAccessibleReporting> {
                    it.element should beInstanceOf<BoundBaseTypeMemberVariable>()
                }
        }

        "access is verified on write" {
            validateModules(
                IntegrationTestModule.of("module_A", """
                    package module_A
                    
                    class Foo {
                        module var x = 3
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fn test() {
                        v = Foo()
                        set v.x = 5
                    }
                """.trimIndent()),
            )
                .shouldReport<ElementNotAccessibleReporting> {
                    it.element should beInstanceOf<BoundBaseTypeMemberVariable>()
                }
        }

        "explicit overexposure export over default module" {
            validateModule("""
                class Foo {
                    export bla: S32 = init
                }
            """.trimIndent())
                .shouldReport<ShadowedVisibilityReporting> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }

        "explicit overexposure export over private" {
            validateModule("""
                private class Foo {
                    export bla: S32 = init
                }
            """.trimIndent())
                .shouldReport<ShadowedVisibilityReporting> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }

        "explicit overexposure explicit module over private" {
            validateModule("""
                private class Foo {
                    module bla: S32 = init
                }
            """.trimIndent())
                .shouldReport<ShadowedVisibilityReporting> {
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
                .shouldReport<ElementNotAccessibleReporting> {
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
                .shouldReport<ElementNotAccessibleReporting> {
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
                .shouldReport<ElementNotAccessibleReporting> {
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
                .shouldReport<ElementNotAccessibleReporting> {
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
                .shouldReport<ElementNotAccessibleReporting> {
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
                    .shouldReport<ElementNotAccessibleReporting> {
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
                    .shouldReport<ElementNotAccessibleReporting> {
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
                    .shouldReport<ElementNotAccessibleReporting> {
                        it.element should beInstanceOf<BoundBaseType>()
                    }
            }
        }
    }

    "voldemort types" - {
        "function parameter" {
            validateModule("""
                private class Foo {}
                module fn test(p: Foo) {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "function parameter type argument" {
            validateModule("""
                export class A<T> {}
                private class B {}
                export fn test(p: A<B>) {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "B"
                }
        }

        "function return type" {
            validateModule("""
                private class Foo {}
                module fn test() -> Foo {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "function return type argument" {
            validateModule("""
                export class A<T> {}
                private class B {}
                intrinsic export fn test() -> A<B>
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "B"
                }
        }

        "function type parameter bound" {
            validateModule("""
                private class Foo {}
                module fn test<T : Foo>() {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "class type parameter bound" {
            validateModule("""
                private class Foo {}
                module class Bar<T : Foo> {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
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
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "Foo"
                }
        }
    }
})