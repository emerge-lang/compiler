package parser.rule

import lexer.*
import matching.Matcher
import matching.ResultCertainty
import parser.MissingTokenReporting
import parser.Reporting
import parser.TokenMismatchReporting
import parser.TokenSequence

interface Rule<T> : Matcher<TokenSequence,T,Reporting> {
    companion object {
        fun singleton(equalTo: Token): Rule<Token> = object : Rule<Token> {
            override val descriptionOfAMatchingThing: String
                get() = equalTo.toString()

            override fun tryMatch(input: TokenSequence): MatchingResult<Token> {
                if (!input.hasNext()) {
                    return MatchingResult(
                            ResultCertainty.DEFINITIVE,
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
                    return MatchingResult(
                            ResultCertainty.DEFINITIVE,
                            token,
                            emptySet()
                    )
                }
                else {
                    input.rollback()
                    return MatchingResult(
                            ResultCertainty.DEFINITIVE,
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

            override fun tryMatch(input: TokenSequence): MatchingResult<Token> {
                if (!input.hasNext()) {
                    return MatchingResult(
                            ResultCertainty.DEFINITIVE,
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
                    return MatchingResult(
                            ResultCertainty.OPTIMISTIC,
                            token,
                            emptySet()
                    )
                }
                else {
                    input.rollback()
                    return MatchingResult(
                            ResultCertainty.DEFINITIVE,
                            null,
                            setOf(
                                    Reporting.error("Expected token of type $type, found $token", token)
                            )
                    )
                }
            }
        }
    }

    override fun describeMismatchOf(seq: TokenSequence): Reporting {
        val result = tryMatch(seq)
        if (result.isSuccess) {
            throw IllegalArgumentException("The given sequence is actually a match - cannot describe mismatch!")
        }

        return result.errors.first()
    }

    override fun tryMatch(input: TokenSequence): MatchingResult<T>
}