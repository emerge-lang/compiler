package compiler.diagnostic

import compiler.ast.AstAnnotation

class DisallowedAnnotationDiagnostic(
    val annotation: AstAnnotation,
    message: String? = null,
) : Diagnostic(
    Severity.ERROR,
    message ?: "Annotations are not allowed here",
    annotation.span,
)