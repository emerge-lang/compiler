package compiler.binding

import compiler.diagnostic.Diagnosis

class BoundAnnotationSet(
    val annotations: List<BoundAnnotation>
) : SemanticallyAnalyzable {
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        annotations.forEach { it.semanticAnalysisPhase1(diagnosis) }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        annotations.forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        annotations.forEach { it.semanticAnalysisPhase3(diagnosis) }
    }
}