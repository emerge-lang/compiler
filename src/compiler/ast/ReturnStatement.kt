package compiler.ast

import compiler.ast.context.CTContext
import compiler.ast.expression.Expression
import compiler.lexer.KeywordToken
import compiler.parser.Reporting

class ReturnStatement(
    val returnKeyword: KeywordToken,
    val expression: Expression
) : Executable {
    override fun validate(context: CTContext): Collection<Reporting> {
        return expression.validate(context)
    }
}