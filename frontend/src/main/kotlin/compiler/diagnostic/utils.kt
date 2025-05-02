import compiler.binding.BoundParameter
import compiler.lexer.Span

internal val BoundParameter.ownershipSpan: Span
    get() = declaration.ownership?.second?.span ?: declaration.span