package compiler.parser

import compiler.InternalCompilerError
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.type.BaseTypeReference
import compiler.lexer.SourceLocation
import compiler.lexer.Token
import compiler.matching.ResultCertainty
import compiler.matching.SimpleMatchingResult
import compiler.parser.rule.RuleMatchingResult
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

    fun <T> toErrorResult(certainty: ResultCertainty = ResultCertainty.DEFINITIVE): RuleMatchingResult<T>
            = SimpleMatchingResult<T,Reporting>(certainty, null, this)

    open override fun toString() = "($level) $message".indentByFromSecondLine(2) + "\nin $sourceLocation"

    enum class Level(val level: Int) {
        CONSECUTIVE(0),
        INFO(10),
        WARNING(20),
        ERROR(30);
    }

    companion object {
        fun consecutive(message: String, sourceLocation: SourceLocation = SourceLocation.UNKNOWN)
            = ConsecutiveFaultReporting(message, sourceLocation)

        fun info(message: String, sourceLocation: SourceLocation)
            = Reporting(Level.INFO, message, sourceLocation)

        fun info(message: String, subjectToken: Token)
            = info(message, subjectToken.sourceLocation)

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

            // type inheritance
            if (!(validatedType.baseType isSubtypeOf targetType.baseType)) {
                message += "; ${validatedType.baseType.simpleName} is not a subtype of ${targetType.baseType.simpleName}"
            }

            // mutability
            val targetModifier = targetType.modifier ?: TypeModifier.MUTABLE
            val validatedModifier = validatedType.modifier ?: TypeModifier.MUTABLE
            if (!(validatedModifier isAssignableTo targetModifier)) {
                message += "; cannot assign ${validatedModifier.name.toLowerCase()} to ${targetModifier.name.toLowerCase()}"
            }

            // void-safety
            if (validatedType.isNullable && !targetType.isNullable) {
                message += "; cannot assign nullable value to non-null reference"
            }

            return error(message, sL)
        }

        fun typeMismatch(targetType: BaseTypeReference, validatedType: BaseTypeReference)
            = typeMismatch(targetType, validatedType, validatedType.original.declaringNameToken?.sourceLocation ?: SourceLocation.UNKNOWN)

        fun unresolvableFunction(expr: BoundInvocationExpression): Reporting {
            // if the receiver type could not be inferred, this is might be a consecutive error
            if (expr.receiverExpression != null && expr.receiverExpression.type == null) {
                return ConsecutiveFaultReporting(
                    "Cannot resolve function ${expr.functionNameToken.value} on receiver of unknown type",
                    expr.declaration.sourceLocation
                )
            }
            else {
                if (expr.context.resolveAnyFunctions(expr.functionNameToken.value).isEmpty()) {
                    // a function with the specified name does not even exist
                    return error("Unknown function ${expr.functionNameToken.value}", expr.functionNameToken)
                }
                else {
                    // type mismatch
                    // TODO: add typescript like error messages here?

                    val parameterListAsString = "(" + expr.parameterExpressions.map { it.toString() }.joinToString(", ") + ")"

                    if (expr.receiverExpression?.type == null) {
                        return error("Function ${expr.functionNameToken.value} is not defined without receiver and parameters $parameterListAsString")
                    }
                    else {
                        return error("Function ${expr.functionNameToken.value} is not defined for receiver ${expr.receiverExpression.type} and parameters $parameterListAsString")
                    }
                }
            }
        }

        fun semanticRecursion(message: String, location: SourceLocation = SourceLocation.UNKNOWN) = error(message, location)
    }
}

class ReportingException(val reporting: Reporting) : Exception(reporting.message)
{
    fun <T> toErrorResult(certainty: ResultCertainty = ResultCertainty.DEFINITIVE): RuleMatchingResult<T>
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

/**
 * An error that results from another one. These should not be shown to an end-user because - assuming the compiler
 * acts as designed - there is another reporting with [Level.ERROR] that describes the root cause.
 */
class ConsecutiveFaultReporting(
        message: String,
        sourceLocation: SourceLocation = SourceLocation.UNKNOWN
) : Reporting(Level.CONSECUTIVE, message, sourceLocation)