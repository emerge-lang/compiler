package compiler.diagnostic

import compiler.InternalCompilerError
import compiler.binding.BoundMemberFunction
import compiler.lexer.Span

class OverrideAccessorDeclarationMismatchDiagnostic private constructor(
    message: String,
    span: Span,
    private val sourceHints: List<SourceHint>,
) : Diagnostic(
    Severity.ERROR,
    message,
    span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateHints(sourceHints)}"

    companion object {
        operator fun invoke(override: BoundMemberFunction, superFn: BoundMemberFunction): OverrideAccessorDeclarationMismatchDiagnostic {
            val overrideAccessorAttr = override.attributes.firstAccessorAttribute
            val superAccessorAttr = superFn.attributes.firstAccessorAttribute
            check(overrideAccessorAttr != superAccessorAttr)

            val message: String
            val span: Span
            val sourceHints = mutableListOf<SourceHint>()
            if (overrideAccessorAttr != null && superAccessorAttr == null) {
                message = "The super function (${superFn.canonicalName}) is not declared as an accessor. The overriding function cannot declare itself an accessor."
                span = overrideAccessorAttr.attributeName.span
                sourceHints.add(SourceHint(span, null))
            } else if (superAccessorAttr != null) {
                val superAccessorText = superAccessorAttr.attributeName.keyword.text
                message = "The super function (${superFn.canonicalName}) is declared $superAccessorText, the override must be declared $superAccessorText, too."
                span = overrideAccessorAttr?.attributeName?.span ?: override.declaredAt
                sourceHints.add(SourceHint(superAccessorAttr.attributeName.span, "super function declared $superAccessorText here", true))
                sourceHints.add(if (overrideAccessorAttr == null) {
                    SourceHint(override.declaredAt, "overriding function not declared $superAccessorText", true)
                } else {
                    SourceHint(overrideAccessorAttr.attributeName.span, "overriding function declared ${overrideAccessorAttr.attributeName.keyword.text} here", true)
                })
            } else {
                throw InternalCompilerError("this is not supposed to happen")
            }

            return OverrideAccessorDeclarationMismatchDiagnostic(message, span, sourceHints)
        }
    }
}