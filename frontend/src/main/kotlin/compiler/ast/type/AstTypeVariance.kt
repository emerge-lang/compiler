package compiler.ast.type

import compiler.lexer.KeywordToken
import compiler.lexer.Span

data class AstTypeVariance(
    val token: KeywordToken,
    val value: TypeVariance,
    val span: Span,
) {
    init {
        require(value != TypeVariance.UNSPECIFIED) {
            "represent an unspecified type variance as a null ${AstTypeVariance::class.simpleName}?"
        }
    }
}