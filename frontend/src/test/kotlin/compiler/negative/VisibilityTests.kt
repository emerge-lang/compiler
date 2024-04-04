package compiler.compiler.negative

import compiler.binding.BoundVariable
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.reportings.ElementNotAccessibleReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.types.beInstanceOf

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
})