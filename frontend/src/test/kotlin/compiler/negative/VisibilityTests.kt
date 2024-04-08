package compiler.compiler.negative

import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundVariable
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.reportings.ElementNotAccessibleReporting
import compiler.reportings.HiddenTypeExposedReporting
import compiler.reportings.ShadowedVisibilityReporting
import io.github.tmarsteel.emerge.backend.api.DotName
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
                    
                    fun dummy() {}
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
                    
                    fun dummy() = x
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
                    fun test() -> Int {
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
                    fun test() {
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
                    export bla: Int = init
                }
            """.trimIndent())
                .shouldReport<ShadowedVisibilityReporting> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }

        "explicit overexposure export over private" {
            validateModule("""
                private class Foo {
                    export bla: Int = init
                }
            """.trimIndent())
                .shouldReport<ShadowedVisibilityReporting> {
                    it.element.shouldBeInstanceOf<BoundBaseTypeMemberVariable>().name shouldBe "bla"
                }
        }

        "explicit overexposure explicit module over private" {
            validateModule("""
                private class Foo {
                    module bla: Int = init
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
                        module fun foo(self) {}
                    }
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.Foo
                    fun test() {
                        v = Foo()
                        v.foo()
                    }
                """.trimIndent()),
            )
                .shouldReport<ElementNotAccessibleReporting> {
                    it.element.shouldBeInstanceOf<BoundDeclaredFunction>().fullyQualifiedName shouldBe DotName(listOf("module_A", "foo"))
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
                    fun test() {
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
                    
                    module fun foo() {}
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.foo
                    fun dummy() {}
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
                    
                    module fun foo() {}
                """.trimIndent()),
                IntegrationTestModule.of("module_B", """
                    package module_B
                    import module_A.*
                    fun test() {
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
                    fun dummy() {}
                """.trimIndent()),
            )
                .shouldReport<ElementNotAccessibleReporting> {
                    it.element should beInstanceOf<BoundBaseTypeDefinition>()
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
                        fun test() -> Foo {}
                    """.trimIndent()),
                )
                    .shouldReport<ElementNotAccessibleReporting> {
                        it.element should beInstanceOf<BoundBaseTypeDefinition>()
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
                        fun test<T : Foo>() {}
                    """.trimIndent()),
                )
                    .shouldReport<ElementNotAccessibleReporting> {
                        it.element should beInstanceOf<BoundBaseTypeDefinition>()
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
                        intrinsic fun test() -> Bar<Foo>
                    """.trimIndent()),
                )
                    .shouldReport<ElementNotAccessibleReporting> {
                        it.element should beInstanceOf<BoundBaseTypeDefinition>()
                    }
            }
        }
    }

    "voldemort types" - {
        "function parameter" {
            validateModule("""
                private class Foo {}
                module fun test(p: Foo) {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "function parameter type argument" {
            validateModule("""
                export class A<T> {}
                private class B {}
                export fun test(p: A<B>) {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "B"
                }
        }

        "function return type" {
            validateModule("""
                private class Foo {}
                module fun test() -> Foo {}
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "Foo"
                }
        }

        "function return type argument" {
            validateModule("""
                export class A<T> {}
                private class B {}
                intrinsic export fun test() -> A<B>
            """.trimIndent())
                .shouldReport<HiddenTypeExposedReporting> {
                    it.type.simpleName shouldBe "B"
                }
        }

        "function type parameter bound" {
            validateModule("""
                private class Foo {}
                module fun test<T : Foo>() {}
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