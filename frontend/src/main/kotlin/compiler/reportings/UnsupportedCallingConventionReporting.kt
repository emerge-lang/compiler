package compiler.reportings

import compiler.ast.AstFunctionAttribute

class UnsupportedCallingConventionReporting(
    val attr: AstFunctionAttribute.External,
    val supportedConventions: Set<String>,
) : Reporting(
    Level.ERROR,
    "The calling-convention/FFI \"${attr.ffiName.value}\" is not supported. Supported currently:\n${supportedConventions.joinToString(separator = "\n", transform = { "- $it" })}",
    attr.sourceLocation,
)