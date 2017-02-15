package parser

import lexer.SourceLocation
import lexer.Token
import parser.rule.MatchingResult
import matching.ResultCertainty
import parser.rule.SimpleMatchingResult

open class Reporting(
    val level: Level,
    val message: String,
    val sourceLocation: SourceLocation
) : Comparable<Reporting>
{
    override fun compareTo(other: Reporting): Int {
        return level.compareTo(other.level)
    }

    fun toException(): ReportingException = ReportingException(this)

    fun <T> toErrorResult(certainty: ResultCertainty = ResultCertainty.DEFINITIVE): MatchingResult<T>
            = SimpleMatchingResult(certainty, null, this)

    open override fun toString() = "($level) $message\n  in $sourceLocation"

    enum class Level(val level: Int) {
        INFO(10),
        WARNING(20),
        ERROR(30);
    }

    companion object {
        fun error(message: String, sourceLocation: SourceLocation)
            = Reporting(Level.ERROR, message, sourceLocation)

        fun error(message: String, erroneousToken: Token)
                = error(message, erroneousToken.sourceLocation!!)

        fun tokenMismatch(expectation: Token): (Token) -> Reporting
        {
            return { erroneousToken -> TokenMismatchReporting(expectation, erroneousToken) }
        }
    }
}

class ReportingException(val reporting: Reporting) : Exception(reporting.message)
{
    fun <T> toErrorResult(certainty: ResultCertainty = ResultCertainty.DEFINITIVE): MatchingResult<T>
            = reporting.toErrorResult(certainty)
}

class TokenMismatchReporting(
        val expected: Token,
        val actual: Token
) : Reporting(Level.ERROR, "Unexpected ${actual.toStringWithoutLocation()}, expected $expected", actual.sourceLocation!!)

class MissingTokenReporting(
        val expected: Token,
        sourceLocation: SourceLocation
) : Reporting(Level.ERROR, "Unexpected EOI, expecting ${expected.toStringWithoutLocation()}", sourceLocation)