package compiler.compiler.negative

import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundVariable
import compiler.binding.classdef.BoundClassConstructor
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.reportings.ElementNotAccessibleReporting
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
                    it.element should beInstanceOf<BoundClassMemberVariable>()
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
                    it.element should beInstanceOf<BoundClassMemberVariable>()
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
})