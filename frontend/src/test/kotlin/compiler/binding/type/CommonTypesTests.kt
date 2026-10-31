package compiler.compiler.binding.type

import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import io.kotest.assertions.withClue
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty

/**
 * The conjectures the proofs in `type-system-proofs/theories` take of [intersect] and
 * [compiler.binding.type.BoundTypeReference.closestCommonSupertypeWith] are checked over [TypeGrid] by Rocq itself,
 * in `OracleGrid.v`, from what [RocqOracleTests] writes of them. This checks what the model can't be asked: that the
 * frontend's intersection stays below both types once their type parameters are instantiated, by the frontend.
 */
class CommonTypesTests : FreeSpec({
    val types = TypeGrid.types

    "the instance of the intersection is below the instances of both types" {
        TypeGrid.instantiations.flatMap { (ctxStr, bindings) ->
            types.flatMap { (aStr, a) ->
                types.mapNotNull { (bStr, b) ->
                    try {
                        val intersection = a.intersect(b).instantiateAllParameters(bindings)
                        val aInstance = a.instantiateAllParameters(bindings)
                        val bInstance = b.instantiateAllParameters(bindings)
                        intersection
                            .takeUnless { it.isBelow(aInstance) && it.isBelow(bInstance) }
                            ?.let { "$aStr, $bStr in $ctxStr: $it, of $aInstance and $bInstance" }
                    } catch (e: Exception) {
                        "$aStr, $bStr in $ctxStr: ${e::class.simpleName} ${e.message}"
                    }
                }
            }
        }.let { violations ->
            withClue(violations.joinToString("\n")) {
                violations.shouldBeEmpty()
            }
        }
    }
})
