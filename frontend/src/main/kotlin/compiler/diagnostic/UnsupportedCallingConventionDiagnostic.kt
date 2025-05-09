package compiler.diagnostic

import compiler.ast.AstFunctionAttribute

class UnsupportedCallingConventionDiagnostic(
    val attr: AstFunctionAttribute.External,
    val supportedConventions: Set<String>,
) : Diagnostic(
    Severity.ERROR,
    "The calling-convention/FFI \"${attr.ffiName.value}\" is not supported. Supported currently:\n${supportedConventions.joinToString(separator = "\n", transform = { "- $it" })}",
    attr.sourceLocation,
)