package compiler.diagnostic

import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.EmergeConstants

class IllegalMainSignatureDiagnostic(
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "The main function takes no parameter, or the root token as its only one: fn main(world: mut ${EmergeConstants.PlatformModule.WORLD_TYPE_NAME})",
    span,
)
