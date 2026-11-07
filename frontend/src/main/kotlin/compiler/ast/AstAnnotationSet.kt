package compiler.ast

import compiler.binding.BoundAnnotation
import compiler.binding.BoundAnnotationSet
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext

class AstAnnotationSet(
    val annotations: List<AstAnnotation>,
) {
    fun bindTo(context: CTContext, lazySubject: () -> Any): BoundAnnotationSet {
        val list = if (annotations.isEmpty()) emptyList<BoundAnnotation>() else {
            val annotationInitCtx = MutableExecutionScopedCTContext.functionRootIn(context)
            return BoundAnnotationSet(annotations.map { it.bindTo(annotationInitCtx, lazySubject) }, lazySubject)
        }

        return BoundAnnotationSet(list, lazySubject)
    }

    companion object {
        val EMPTY = AstAnnotationSet(emptyList())
    }
}