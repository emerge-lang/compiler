package compiler.parser.rule

import compiler.lexer.Token
import compiler.lexer.TokenType
import compiler.matching.Matcher
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.reportings.MissingTokenReporting
import compiler.reportings.Reporting
import compiler.reportings.TokenMismatchReporting

interface Rule<T> : Matcher<TokenSequence,T, Reporting> {
    companion object {
        fun singleton(equalTo: Token, mismatchCertainty: ResultCertainty = ResultCertainty.NOT_RECOGNIZED): Rule<Token> = object : Rule<Token> {
            override val descriptionOfAMatchingThing: String
                get() = equalTo.toString()

            override fun tryMatch(input: TokenSequence): RuleMatchingResult<Token> {
                if (!input.hasNext()) {
                    return RuleMatchingResultImpl(
                        mismatchCertainty,
                        null,
                        setOf(
                            MissingTokenReporting(equalTo, input.currentSourceLocation)
                        )
                    )
                }

                input.mark()

                val token = input.next()!!
                if (token == equalTo) {
                    input.commit()
                    return RuleMatchingResultImpl(
                        ResultCertainty.DEFINITIVE,
                        token,
                        emptySet()
                    )
                }
                else {
                    input.rollback()
                    return RuleMatchingResultImpl(
                        mismatchCertainty,
                        null,
                        setOf(
                            TokenMismatchReporting(equalTo, token)
                        )
                    )
                }
            }
        }

        fun singletonOfType(type: TokenType): Rule<Token> = object : Rule<Token> {
            override val descriptionOfAMatchingThing: String
                get() = type.name

            override fun tryMatch(input: TokenSequence): RuleMatchingResult<Token> {
                if (!input.hasNext()) {
                    return RuleMatchingResultImpl(
                        ResultCertainty.NOT_RECOGNIZED,
                        null,
                        setOf(
                            Reporting.error("Expected token of type $type, found nothing", input.currentSourceLocation)
                        )
                    )
                }

                input.mark()

                val token = input.next()!!
                if (token.type == type) {
                    input.commit()
                    return RuleMatchingResultImpl(
                        ResultCertainty.OPTIMISTIC,
                        token,
                        emptySet()
                    )
                }
                else {
                    input.rollback()
                    return RuleMatchingResultImpl(
                        ResultCertainty.NOT_RECOGNIZED,
                        null,
                        setOf(
                                Reporting.error("Expected token of type $type, found $token", token)
                        )
                    )
                }
            }
        }
    }

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<T>
}