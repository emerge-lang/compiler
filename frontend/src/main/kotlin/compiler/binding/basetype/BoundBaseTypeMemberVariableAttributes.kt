package compiler.binding.basetype

import compiler.diagnostic.Diagnosis
import compiler.diagnostic.duplicateMemberVariableAttributes
import compiler.diagnostic.invalidMemberVariableAttribute
import compiler.lexer.KeywordToken

class BoundBaseTypeMemberVariableAttributes(
    val astNodes: List<KeywordToken>,
) {
    fun validate(diagnosis: Diagnosis) {
        val (applicableAttrs, inapplicableAttrs) = astNodes.partition { false } /* no attributes known currently */
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