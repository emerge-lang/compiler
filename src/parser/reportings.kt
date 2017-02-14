package parser

import lexer.SourceLocation
import lexer.Token
import lexer.TokenType
import parser.rule.MatchingResult
import matching.ResultCertainty
import parser.rule.SimpleMatchingResult

data class Reporting(
    val level: Level,
    val type: ReportingType,
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

    enum class Level(val level: Int) {
        INFO(10),
        WARNING(20),
        ERROR(30);
    }

    companion object {
        fun error(type: ReportingType, message: String, sourceLocation: SourceLocation)
            = Reporting(Level.ERROR, type, message, sourceLocation)

        fun error(type: ReportingType, message: String, erroneousToken: Token)
                = error(type, message, erroneousToken.sourceLocation)

        fun tokenMismatch(expectation: String, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): (Token) -> Reporting
        {
            return { erroneousToken ->
                Reporting(
                    Reporting.Level.ERROR,
                    ReportingType.TOKEN_MISMATCH,
                    "expected $expectation but found $erroneousToken",
                    erroneousToken.sourceLocation
                )
            }
        }

        fun tokenMismatch(expectedType: TokenType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): (Token) -> Reporting
            = tokenMismatch(expectedType.name, certainty)
    }
}

class ReportingException(val reporting: Reporting) : Exception(reporting.message)
{
    fun <T> toErrorResult(certainty: ResultCertainty = ResultCertainty.DEFINITIVE): MatchingResult<T>
            = reporting.toErrorResult(certainty)
}

enum class ReportingType {
    TOKEN_MISMATCH,
    MISSING_TOKEN
}