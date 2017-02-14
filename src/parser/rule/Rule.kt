package parser.rule

import lexer.*
import matching.Matcher
import matching.PredicateMatcher
import parser.Reporting
import parser.ReportingException
import parser.ReportingType
import parser.TokenSequence

interface Rule<T> : Matcher<TokenSequence,T,Reporting> {
    companion object {
        fun singleton(predicate: PredicateMatcher<Token, Reporting>) = object: Rule<Sequence<Token>> {
            override val descriptionOfAMatchingThing = predicate.descriptionOfAMatchingThing

            override fun tryMatch(input: TokenSequence): MatchingResult<Sequence<Token>> {
                try
                {
                    return successfulMatch(sequenceOf(
                            input.transact
                            {
                                val token = input.next()!!
                                if (predicate(token)) {
                                    return@transact token
                                } else {
                                    throw predicate.describeMismatchOf(token).toException()
                                }
                            }
                    ))
                }
                catch (ex: ReportingException)
                {
                    return ex.toErrorResult()
                }
            }

            override fun describeMismatchOf(seq: TokenSequence): Reporting {
                if (seq.hasNext())
                {
                    return predicate.describeMismatchOf(seq.next()!!)
                }
                else
                {
                    return Reporting.error(
                            ReportingType.MISSING_TOKEN,
                            "Expected ${predicate.descriptionOfAMatchingThing} but input had no more tokens",
                            seq.currentSourceLocation
                    )
                }
            }
        }
    }

    override fun describeMismatchOf(seq: TokenSequence): Reporting {
        val result = tryMatch(seq) as MatchingResult<T>
        if (result.isSuccess) {
            throw IllegalArgumentException("The given sequence is actually a match - cannot describe mismatch!")
        }

        return result.errors.first()
    }
}