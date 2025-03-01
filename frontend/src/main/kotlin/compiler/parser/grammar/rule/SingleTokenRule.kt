package compiler.parser.grammar.rule

import compiler.InternalCompilerError
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.diagnostic.Diagnostic

abstract class SingleTokenRule<Item : Token>(
    override val explicitName: String,

    /**
     * Like the argument to [Iterable.mapNotNull]: token of the correct type if it fits, null otherwise. Intended
     * to be used with the `as?` operator
     */
    private val filterAndCast: (Token) -> Item?,
) : Rule<Item> {
    override fun toString() = explicitName

    override fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<Item>> {
        return sequence {
            for (index in atIndex..tokens.lastIndex) {
                val token = tokens[index]
                val filteredToken = filterAndCast(token)
                if (filteredToken != null) {
                    yield(MatchingResult.Success(filteredToken, index + 1))
                    return@sequence
                }
                if (canIgnore(token)) {
                    continue
                }
                yield(MatchingResult.Error(Diagnostic.parsingMismatch(explicitName, token)))
                return@sequence
            }

            throw InternalCompilerError("This should never happen as there is always an EOI token at the end of the token stream.")
        }
    }

    private companion object {
        @JvmStatic
        fun canIgnore(token: Token) = token is OperatorToken && token.operator == Operator.NEWLINE
    }
}

