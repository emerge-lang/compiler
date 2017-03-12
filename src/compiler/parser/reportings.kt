package compiler.parser

import compiler.InternalCompilerError
import compiler.ast.type.BaseTypeReference
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation
import compiler.lexer.Token
import compiler.parser.rule.MatchingResult
import compiler.matching.ResultCertainty
import compiler.parser.rule.SimpleMatchingResult
import textutils.indentByFromSecondLine

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

    open override fun toString() = "($level) $message".indentByFromSecondLine(2) + "\nin $sourceLocation"

    enum class Level(val level: Int) {
        INFO(10),
        WARNING(20),
        ERROR(30);
    }

    companion object {
        fun error(message: String, sourceLocation: SourceLocation)
            = Reporting(Level.ERROR, message, sourceLocation)

        fun error(message: String, erroneousToken: Token)
            = error(message, erroneousToken.sourceLocation)

        fun unexpectedEOI(expected: String, erroneousLocation: SourceLocation)
            = error("Unexpected EOI, expected $expected", erroneousLocation)

        fun tokenMismatch(expectation: Token): (Token) -> Reporting
        {
            return { erroneousToken -> TokenMismatchReporting(expectation, erroneousToken) }
        }

        fun unknownType(erroneousRef: TypeReference) =
            if (erroneousRef.declaringNameToken != null) {
                error("Cannot resolve type ${erroneousRef.declaredName}", erroneousRef.declaringNameToken)
            }
            else {
                error("Cannot resolve type ${erroneousRef.declaredName}", SourceLocation.UNKNOWN)
            }

        fun typeMismatch(targetType: BaseTypeReference, validatedType: BaseTypeReference, sL: SourceLocation): Reporting {
            if (validatedType isAssignableTo targetType) throw InternalCompilerError("wtf?!")

            var message = "Cannot assign a value of type $validatedType to a reference of type $targetType"

            if (!(validatedType.baseType isSubtypeOf targetType.baseType)) {
                message += "; ${validatedType.baseType.simpleName} is not a subtype of ${targetType.baseType.simpleName}"
            }

            val targetModifier = targetType.modifier ?: TypeModifier.MUTABLE
            val validatedModifier = validatedType.modifier ?: TypeModifier.MUTABLE
            if (!(validatedModifier isAssignableTo targetModifier)) {
                message += "; cannot assign ${validatedModifier.name.toLowerCase()} to ${targetModifier.name.toLowerCase()}"
            }

            return error(message, sL)
        }

        fun typeMismatch(targetType: BaseTypeReference, validatedType: BaseTypeReference)
            = typeMismatch(targetType, validatedType, validatedType.original.declaringNameToken?.sourceLocation ?: SourceLocation.UNKNOWN)
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
) : Reporting(Level.ERROR, "Unexpected ${actual.toStringWithoutLocation()}, expected $expected", actual.sourceLocation)

class MissingTokenReporting(
        val expected: Token,
        sourceLocation: SourceLocation
) : Reporting(Level.ERROR, "Unexpected EOI, expecting ${expected.toStringWithoutLocation()}", sourceLocation)