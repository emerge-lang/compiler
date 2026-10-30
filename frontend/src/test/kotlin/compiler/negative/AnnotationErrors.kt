package compiler.compiler.negative

import compiler.diagnostic.PurityViolationDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.types.shouldBeInstanceOf

class AnnotationErrors : FreeSpec({
    "mutates or reads global state" {
        for (kw in listOf("mut", "read")) {
            validateModule("""
                intrinsic $kw fn x() -> S32
                #[x()]
                class A {
                }
            """.trimIndent())
                .shouldFind<PurityViolationDiagnostic> {
                    it.boundary.shouldBeInstanceOf<PurityViolationDiagnostic.SideEffectBoundary.Annotation>()
                }
        }
    }
})