package compiler.diagnostic

import compiler.ast.AstAnnotation
import compiler.binding.type.BoundTypeReference
import io.github.tmarsteel.emerge.common.EmergeConstants

class ValueNotAnnotatableDiagnostic(
    val annotation: AstAnnotation,
    val type: BoundTypeReference?,
) : Diagnostic(
    Severity.ERROR,
    run {
        var message = "Annotations can only store instances of classes that are themselves annotated with ${EmergeConstants.CoreModule.ANNOTATABLE_TYPE_NAME}"
        if (type != null) {
            message += "\nValues of type $type do not satisfy this requirement."
        }
        message
    },
    annotation.span,
)