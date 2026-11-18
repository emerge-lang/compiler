package compiler.diagnostic

import compiler.binding.basetype.BoundBaseType
import compiler.diagnostic.rendering.CellBuilder
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
    run {
        var message = "This `${Keyword.WHEN.text}` is used as a value, it needs an `${Keyword.ELSE.text}` branch"
        message += if (reasonSubjectTypeIsOpen == null) {
            " or cover all possible cases."
        } else {
            ".\nExhaustiveness cannot be verified because $reasonSubjectTypeIsOpen"
        }

        message
    },
    keyword.span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        val missingCases = missingClasses.map { "${Keyword.INSTANCEOF.text} ${it.canonicalName}" } +
                listOfNotNull("null".takeIf { missesNull })

        if (reasonSubjectTypeIsOpen == null && missingCases.isNotEmpty()) {
            builder.assureOnBlankLine()
            builder.text("Uncovered cases that, if covered, remove the need for an ${Keyword.ELSE.text} branch:")
            for (missingCase in missingCases) {
                builder.assureOnBlankLine()
                builder.text("- $missingCase")
            }
            builder.assureOnBlankLine()
            builder.appendLineBreak()
        }

        super.renderBody()
    }
}
