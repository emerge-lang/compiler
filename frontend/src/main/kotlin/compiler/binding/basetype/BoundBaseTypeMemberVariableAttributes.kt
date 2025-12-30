package compiler.binding.basetype

import compiler.ast.AstBaseTypeMemberVariableAttribute
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.conflictingMemberVariableAttributes
import compiler.diagnostic.duplicateMemberVariableAttributes
import compiler.util.twoElementPermutationsUnordered

class BoundBaseTypeMemberVariableAttributes(
    val attributes: List<AstBaseTypeMemberVariableAttribute>,
) {
    val ownershipAttribute: AstBaseTypeMemberVariableAttribute.Ownership? = attributes
        .filterIsInstance<AstBaseTypeMemberVariableAttribute.Ownership>()
        .firstOrNull()

    val ownership = ownershipAttribute?.ownership ?: BoundBaseTypeMemberVariable.Ownership.OWNED

    fun validate(diagnosis: Diagnosis) {
        attributes
            .groupBy { it.attributeName.keyword }
            .values
            .filter { it.size > 1 }
            .forEach { dupes ->
                diagnosis.duplicateMemberVariableAttributes(dupes.first(), dupes.drop(1))
            }

        attributes.twoElementPermutationsUnordered()
            .filter { (a, b) -> a.conflictsWith(b) }
            .forEach { (a, b) ->
                diagnosis.conflictingMemberVariableAttributes(listOf(a, b))
            }
    }
}