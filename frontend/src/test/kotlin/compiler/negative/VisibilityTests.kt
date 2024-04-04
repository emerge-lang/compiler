package compiler.compiler.negative

import compiler.binding.BoundVariable
import compiler.reportings.ElementNotAccessibleReporting
import io.kotest.core.spec.style.FreeSpec
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
                    it.element.shouldBeInstanceOf<BoundVariable>()
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
                    it.element.shouldBeInstanceOf<BoundVariable>()
                }
        }
    }
})