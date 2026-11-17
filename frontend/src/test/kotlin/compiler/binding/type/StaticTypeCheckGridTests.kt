package compiler.compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.StaticTypeCheckResult
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.ints.shouldBeGreaterThan

/**
 * [StaticTypeCheckResult.of] over [TypeGrid]: what it says of a check has to agree with the subtype relation, which
 * is what the check at runtime decides by (`RuntimeSubtypingGridTests` holds the two together).
 */
class StaticTypeCheckGridTests : FreeSpec({
    /**
     * the types an object can be of: a class with exact type arguments. What a check is run on is such a type, with
     * the mutability of the reference to the object.
     */
    val objectTypes = TypeGrid.types.filter { (name, type) ->
        type is RootResolvedTypeReference
            && !type.baseType.kind.allowsSubtypes
            && !type.isNonNullableNothing
            && TypeGrid.ctxParameters.none { it in Regex("[A-Za-z]+").findAll(name).map { m -> m.value } }
            && type.arguments.orEmpty().all { it.variance == TypeVariance.UNSPECIFIED }
    }

    "a check that is said to never succeed has no object it succeeds for" {
        objectTypes.size shouldBeGreaterThan 10

        var nNeverSucceeds = 0
        val violations = mutableListOf<String>()
        for ((nameOfValueType, typeOfValue) in TypeGrid.types) {
            for ((nameOfTypeToCheck, typeToCheck) in TypeGrid.types) {
                val result = StaticTypeCheckResult.of(typeOfValue, typeToCheck)
                if (result !is StaticTypeCheckResult.NeverSucceeds) {
                    continue
                }
                nNeverSucceeds++

                if (typeOfValue.isNullable && typeToCheck.isNullable) {
                    violations.add("($nameOfValueType) is ($nameOfTypeToCheck) succeeds for null, but: ${result.reason}")
                }
                for ((nameOfObjectType, objectType) in objectTypes) {
                    val asReferred: BoundTypeReference = objectType.withMutability(typeOfValue.mutability)
                    if (asReferred.isSubtypeOf(typeOfValue) && asReferred.isSubtypeOf(typeToCheck)) {
                        violations.add("($nameOfValueType) is ($nameOfTypeToCheck) succeeds for a $nameOfObjectType referred to as $asReferred, but: ${result.reason}")
                    }
                }
            }
        }

        violations.shouldBeNone()
        nNeverSucceeds shouldBeGreaterThan 1000
    }

    "a check is said to always succeed exactly where the value is of a subtype" {
        val violations = mutableListOf<String>()
        for ((nameOfValueType, typeOfValue) in TypeGrid.types) {
            if (typeOfValue.isNonNullableNothing) {
                continue
            }
            for ((nameOfTypeToCheck, typeToCheck) in TypeGrid.types) {
                val alwaysSucceeds = StaticTypeCheckResult.of(typeOfValue, typeToCheck) == StaticTypeCheckResult.AlwaysSucceeds
                if (alwaysSucceeds != typeOfValue.isSubtypeOf(typeToCheck)) {
                    violations.add("($nameOfValueType) is ($nameOfTypeToCheck)")
                }
            }
        }

        violations.shouldBeNone()
    }
})
