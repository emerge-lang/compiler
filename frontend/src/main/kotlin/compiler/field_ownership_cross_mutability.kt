package compiler

import compiler.FOCMResult.Action.READ
import compiler.FOCMResult.Action.WRITE
import compiler.FieldOwnership.OWN
import compiler.FieldOwnership.REF
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeMutability.EXCLUSIVE
import compiler.ast.type.TypeMutability.IMMUTABLE
import compiler.ast.type.TypeMutability.MUTABLE
import compiler.ast.type.TypeMutability.READCONST
import compiler.ast.type.TypeMutability.READONLY

enum class FieldOwnership {
    REF,
    OWN,
    ;
}

data class FOCMResult(
    val referenceMutability: TypeMutability,
    val fieldOwnership: FieldOwnership,
    val fieldMutability: TypeMutability,
    val action: Action,
    val isAllowed: Boolean,
    val mutabilityAfterDeref: TypeMutability?,
) {
    override fun toString() = "${referenceMutability.keyword.text} ref, ${fieldOwnership.name.lowercase()} ${fieldMutability.keyword.text} field"

    enum class Action {
        READ,
        WRITE,
        ;
    }
}

fun main() {
    data
        .filter { it.action == READ && it.referenceMutability != READONLY }
        .onEach { check(it.mutabilityAfterDeref != null) }
        .flatMap {
            mutabilityHierarchy.getValue(it.referenceMutability)
                .map { superM ->
                    val resultForReadRefMutability = data.single { c ->
                        c.referenceMutability == READONLY && c.fieldOwnership == it.fieldOwnership && c.fieldMutability == it.fieldMutability && c.action == it.action
                    }

                    it to resultForReadRefMutability
                }
        }
        .filter { (r, rForSuperM) -> !r.mutabilityAfterDeref!!.isAssignableTo(rForSuperM.mutabilityAfterDeref!!) }
        .forEach { (r, rForSuperM) ->
            println("Error: $r; yields ${r.mutabilityAfterDeref} but ${rForSuperM.referenceMutability.keyword.text} ref yields ${rForSuperM.mutabilityAfterDeref!!.keyword.text}")
        }
}

private val mutabilityHierarchy: Map<TypeMutability, Set<TypeMutability>> = enumValues<TypeMutability>().associateWith { subM ->
    enumValues<TypeMutability>().filter { superM -> subM.isAssignableTo(superM) }.toSet() - setOf(subM)
}

private val data = listOf<FOCMResult>(
    FOCMResult(MUTABLE, OWN, MUTABLE, READ, true, MUTABLE),
    FOCMResult(MUTABLE, OWN, MUTABLE, WRITE, true, null),
    FOCMResult(MUTABLE, OWN, READONLY, READ, true, READONLY),
    FOCMResult(MUTABLE, OWN, READONLY, WRITE, true, null),
    FOCMResult(MUTABLE, OWN, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(MUTABLE, OWN, IMMUTABLE, WRITE, true, null),
    FOCMResult(READONLY, OWN, MUTABLE, READ, true, READCONST),
    FOCMResult(READONLY, OWN, MUTABLE, WRITE, false, null),
    FOCMResult(READONLY, OWN, READONLY, READ, true, READCONST),
    FOCMResult(READONLY, OWN, READONLY, WRITE, false, null),
    FOCMResult(READONLY, OWN, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(READONLY, OWN, IMMUTABLE, WRITE, false, null),
    FOCMResult(IMMUTABLE, OWN, MUTABLE, READ, true, READCONST),
    FOCMResult(IMMUTABLE, OWN, MUTABLE, WRITE, false, null),
    FOCMResult(IMMUTABLE, OWN, READONLY, READ, true, READCONST),
    FOCMResult(IMMUTABLE, OWN, READONLY, WRITE, false, null),
    FOCMResult(IMMUTABLE, OWN, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(IMMUTABLE, OWN, IMMUTABLE, WRITE, false, null),
    FOCMResult(EXCLUSIVE, OWN, MUTABLE, READ, true, MUTABLE),
    FOCMResult(EXCLUSIVE, OWN, MUTABLE, WRITE, true, null),
    FOCMResult(EXCLUSIVE, OWN, READONLY, READ, true, READONLY),
    FOCMResult(EXCLUSIVE, OWN, READONLY, WRITE, true, null),
    FOCMResult(EXCLUSIVE, OWN, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(EXCLUSIVE, OWN, IMMUTABLE, WRITE, true, null),
    FOCMResult(READCONST, OWN, MUTABLE, READ, true, READCONST),
    FOCMResult(READCONST, OWN, MUTABLE, WRITE, false, null),
    FOCMResult(READCONST, OWN, READONLY, READ, true, READCONST),
    FOCMResult(READCONST, OWN, READONLY, WRITE, false, null),
    FOCMResult(READCONST, OWN, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(READCONST, OWN, IMMUTABLE, WRITE, false, null),
    FOCMResult(READCONST, REF, MUTABLE, READ, true, READCONST),
    FOCMResult(READCONST, REF, MUTABLE, WRITE, false, null),
    FOCMResult(READCONST, REF, READONLY, READ, true, READCONST),
    FOCMResult(READCONST, REF, READONLY, WRITE, false, null),
    FOCMResult(READCONST, REF, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(READCONST, REF, IMMUTABLE, WRITE, false, null),
    FOCMResult(MUTABLE, REF, MUTABLE, READ, true, MUTABLE),
    FOCMResult(MUTABLE, REF, MUTABLE, WRITE, true, null),
    FOCMResult(MUTABLE, REF, READONLY, READ, true, READONLY),
    FOCMResult(MUTABLE, REF, READONLY, WRITE, true, null),
    FOCMResult(MUTABLE, REF, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(MUTABLE, REF, IMMUTABLE, WRITE, true, null),
    FOCMResult(READONLY, REF, MUTABLE, READ, true, READONLY),
    FOCMResult(READONLY, REF, MUTABLE, WRITE, false, null),
    FOCMResult(READONLY, REF, READONLY, READ, true, READONLY),
    FOCMResult(READONLY, REF, READONLY, WRITE, false, null),
    FOCMResult(READONLY, REF, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(READONLY, REF, IMMUTABLE, WRITE, false, null),
    FOCMResult(IMMUTABLE, REF, MUTABLE, READ, true, MUTABLE),
    FOCMResult(IMMUTABLE, REF, MUTABLE, WRITE, false, null),
    FOCMResult(IMMUTABLE, REF, READONLY, READ, true, READONLY),
    FOCMResult(IMMUTABLE, REF, READONLY, WRITE, false, null),
    FOCMResult(IMMUTABLE, REF, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(IMMUTABLE, REF, IMMUTABLE, WRITE, false, null),
    FOCMResult(EXCLUSIVE, REF, MUTABLE, READ, true, MUTABLE),
    FOCMResult(EXCLUSIVE, REF, MUTABLE, WRITE, true, null),
    FOCMResult(EXCLUSIVE, REF, READONLY, READ, true, READONLY),
    FOCMResult(EXCLUSIVE, REF, READONLY, WRITE, true, null),
    FOCMResult(EXCLUSIVE, REF, IMMUTABLE, READ, true, IMMUTABLE),
    FOCMResult(EXCLUSIVE, REF, IMMUTABLE, WRITE, true, null),
)