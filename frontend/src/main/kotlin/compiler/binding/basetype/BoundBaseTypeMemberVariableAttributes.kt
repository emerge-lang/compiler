package compiler.binding.basetype

import compiler.diagnostic.Diagnosis
import compiler.diagnostic.duplicateMemberVariableAttributes
import compiler.diagnostic.invalidMemberVariableAttribute
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken

class BoundBaseTypeMemberVariableAttributes(
    val astNodes: List<KeywordToken>,
) {
    val firstDecoratesAttribute: KeywordToken? = astNodes.firstOrNull { it.keyword == Keyword.DECORATES }

    fun validate(diagnosis: Diagnosis) {
        val (applicableAttrs, inapplicableAttrs) = astNodes.partition { it.keyword == Keyword.DECORATES }
        inapplicableAttrs.forEach {
            diagnosis.invalidMemberVariableAttribute(it, "${it.keyword.text} is not a valid attribute on member variables")
        }

        applicableAttrs
            .groupBy { it.keyword }
            .values
            .filter { it.size > 1 }
            .forEach { dupes ->
                diagnosis.duplicateMemberVariableAttributes(dupes.first(), dupes.drop(1))
            }
    }
}