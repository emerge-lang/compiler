package compiler.binding.expression

import compiler.binding.basetype.BoundBaseType
import compiler.binding.type.PossibleRuntimeTypes

/**
 * Determines whether the `is` (and `null`) branches of a `when` with a subject cover all values the subject
 * can have at runtime.
 */
class WhenExhaustiveness(
    /** whether the `when` has a `null -> ...` branch */
    val hasNullBranch: Boolean,
) {
    private val instanceOfChecks = ArrayList<BoundInstanceOfExpression>()

    /** to be called while binding, once for each `is` branch, in the order of the branches */
    fun registerInstanceOfCheck(check: BoundInstanceOfExpression) {
        instanceOfChecks.add(check)
    }

    /**
     * Only available once semantic analysis phase 2 is done for all the conditions of the `when`.
     */
    val result: Result by lazy {
        val firstCheck = instanceOfChecks.firstOrNull() ?: return@lazy Result.Unknown
        val subjectType = firstCheck.expressionToCheck.type ?: return@lazy Result.Unknown
        val possibleTypes = when (val possible = subjectType.possibleRuntimeTypes()) {
            is PossibleRuntimeTypes.Open -> return@lazy Result.SubjectTypeIsOpen(possible.reason)
            is PossibleRuntimeTypes.Closed -> possible
        }

        val remainingClasses = LinkedHashSet(possibleTypes.classes)
        for (check in instanceOfChecks) {
            val typeToCheck = check.typeToCheck ?: return@lazy Result.Unknown
            if (!typeToCheck.subtypeCheckWithRequiresOnlyBaseType(check.expressionToCheck.type)) {
                // conservative: the check may fail for some objects of the class
                continue
            }
            val baseTypeToCheck = typeToCheck.baseTypeOfLowerBound
            remainingClasses.removeIf { it isSubtypeOf baseTypeToCheck }
        }

        val missesNull = possibleTypes.includesNull && !hasNullBranch
        if (remainingClasses.isEmpty() && !missesNull) {
            Result.Exhaustive
        } else {
            Result.NotExhaustive(remainingClasses, missesNull)
        }
    }

    sealed interface Result {
        /** the branches cover all values the subject can have */
        data object Exhaustive : Result

        /** there are errors in the subject or the branches, so exhaustiveness can't be determined */
        data object Unknown : Result

        /** the compiler can't know all the subtypes of the subject, see [PossibleRuntimeTypes.Open] */
        data class SubjectTypeIsOpen(val reason: String) : Result

        data class NotExhaustive(val missingClasses: Set<BoundBaseType>, val missesNull: Boolean) : Result
    }
}
