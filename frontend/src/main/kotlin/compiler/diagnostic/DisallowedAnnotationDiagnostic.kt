package compiler.diagnostic

import compiler.ast.AstAnnotation

class DisallowedAnnotationDiagnostic(
    val annotation: AstAnnotation,
) : Diagnostic(
    Severity.ERROR,
    "Annotations are not allowed here",
    annotation.span,
)