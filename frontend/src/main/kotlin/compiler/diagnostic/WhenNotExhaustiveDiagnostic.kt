package compiler.diagnostic

import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken

/**
 * A `when` with `is` branches and without an `else` branch is used as a value, but the branches don't cover all
 * the values its subject can have.
 */
class WhenNotExhaustiveDiagnostic(
    val keyword: KeywordToken,
    /** the classes that no branch covers; empty if [reasonSubjectTypeIsOpen] is given */
    val missingClasses: Set<BoundBaseType>,
    val missesNull: Boolean,
    /** if not null: the compiler can't know all subtypes of the subject, see [compiler.binding.type.PossibleRuntimeTypes.Open] */
    val reasonSubjectTypeIsOpen: String?,
) : Diagnostic(
    Severity.ERROR,
    buildMessage(missingClasses, missesNull, reasonSubjectTypeIsOpen),
    keyword.span,
) {
    override fun toString() = super.toString()

    private companion object {
        fun buildMessage(missingClasses: Set<BoundBaseType>, missesNull: Boolean, reasonSubjectTypeIsOpen: String?): String {
            val prefix = "This `${Keyword.WHEN.text}` is used as a value, it needs an `${Keyword.ELSE.text}` branch"
            if (reasonSubjectTypeIsOpen != null) {
                return "$prefix: $reasonSubjectTypeIsOpen"
            }

            val missingCases = missingClasses.map { "`${Keyword.INSTANCEOF.text} ${it.canonicalName}`" } +
                listOfNotNull("`null`".takeIf { missesNull })
            return "$prefix or branches for all of these cases: ${missingCases.joinToString()}"
        }
    }
}
