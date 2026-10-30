package compiler.binding

import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import io.github.tmarsteel.emerge.common.CanonicalElementName

class BoundAnnotationSet(
    val annotations: List<BoundAnnotation>,
    subjectGetter: () -> Any,
) : SemanticallyAnalyzable {
    val subject by lazy(subjectGetter)

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        annotations.forEach { it.semanticAnalysisPhase1(diagnosis) }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        annotations.forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        annotations.forEach { it.semanticAnalysisPhase3(diagnosis) }
    }

    fun anyOfType(typeName: CanonicalElementName) = annotations.any {
        val type = it.type as? RootResolvedTypeReference ?: return@any false
        type.baseType.canonicalName == typeName
    }
}