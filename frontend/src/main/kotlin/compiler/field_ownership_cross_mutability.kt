package compiler

import compiler.FieldOwnership.OWN
import compiler.FieldOwnership.REF
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeMutability.EXCLUSIVE
import compiler.ast.type.TypeMutability.IMMUTABLE
import compiler.ast.type.TypeMutability.MUTABLE
import compiler.ast.type.TypeMutability.READCONST
import compiler.ast.type.TypeMutability.READONLY

/**
 * REF means the mutability after dereference is always as stated on the field, independent of the mutability of the holding object
 * OWN means the mutability after dereference is inferred from the mutability of the holding object, no explicit
 * mutability can be specified. Also, OWN fields must be initialized with an exclusive value either by init expr
 * or by constructor parameter.
 *
 * If these semantics ([deriveMutabilityAfterDeref] and [deriveAllowWrite]) are taken into the compiler, the
 * type system should be sound again. Constructors are the no longer a shortcut to create both a mut and a const
 * reference to the same object
 */

enum class FieldOwnership {
    REF,
    OWN,
    ;
}

data class FieldSpec(
    val referenceMutability: TypeMutability,
    val fieldOwnership: FieldOwnership,
    val fieldMutability: TypeMutability,
) {
    override fun toString() = "${referenceMutability.keyword.text} Holder; ${fieldOwnership.name.lowercase()} m: ${fieldMutability.keyword.text} Any;"
}


fun main() {
    val fieldSpecs = sequence {
        enumValues<TypeMutability>().forEach { referenceMutability ->
            enumValues<FieldOwnership>().forEach { fieldOwnership ->
                enumValues<TypeMutability>().filter { it != EXCLUSIVE }.forEach { fieldMutability ->
                    yield(FieldSpec(referenceMutability, fieldOwnership, fieldMutability))
                }
            }
        }
    }

    fieldSpecs
        .filter { it.referenceMutability != EXCLUSIVE }
        .forEach { fieldSpec ->
            mutabilityHierarchy.getValue(fieldSpec.referenceMutability).forEach { superM ->
                val superSpec = fieldSpec.copy(referenceMutability = superM)
                val selfDeref = fieldSpec.deriveMutabilityAfterDeref()
                val superDeref = superSpec.deriveMutabilityAfterDeref()
                check(selfDeref.isAssignableTo(superDeref)) {
                    "$fieldSpec -> $selfDeref, $superSpec -> $superDeref ; $superDeref is not assignable to $selfDeref"
                }
            }
        }

    fieldSpecs
        .filter { it.referenceMutability == EXCLUSIVE }
        .filter { it.fieldOwnership == OWN }
        .forEach { fieldSpec ->
            listOf(READCONST, READONLY, MUTABLE, IMMUTABLE).forEach { mutability ->
                check(fieldSpec.deriveAllowWrite(mutability) == false) {
                    "it should be impossible to assign ${mutability.keyword.text} to $fieldSpec"
                }
            }
            check(fieldSpec.deriveAllowWrite(EXCLUSIVE) == true)
        }

    fieldSpecs
        .filter { it.deriveMutabilityAfterDeref() == EXCLUSIVE }
        .forEach {
            error("This should be impossible: $it")
        }
}

private val mutabilityHierarchy: Map<TypeMutability, 
    Set<TypeMutability>> = enumValues<TypeMutability>().associateWith { subM ->
    enumValues<TypeMutability>().filter { superM -> subM.isAssignableTo(superM) }.toSet() - setOf(subM)
}

private fun FieldSpec.deriveMutabilityAfterDeref(): TypeMutability {
    return when (fieldOwnership) {
        OWN -> when (referenceMutability) {
            EXCLUSIVE -> READCONST
            else -> referenceMutability
        }
        REF -> fieldMutability
    }
}
private fun FieldSpec.deriveAllowWrite(mutabilityOfValueToAssign: TypeMutability): Boolean {
    when (fieldOwnership) {
        OWN -> when (referenceMutability) {
            EXCLUSIVE -> return mutabilityOfValueToAssign == EXCLUSIVE
            else -> return mutabilityOfValueToAssign.isAssignableTo(deriveMutabilityAfterDeref())
        }
        REF -> return mutabilityOfValueToAssign.isAssignableTo(fieldMutability)
    }
}