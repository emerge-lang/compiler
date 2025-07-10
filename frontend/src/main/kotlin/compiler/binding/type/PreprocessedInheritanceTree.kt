package compiler.binding.type

import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundSupertypeDeclaration
import io.github.tmarsteel.emerge.common.zip
import java.util.IdentityHashMap

open class PartialPreprocessedInheritanceTree(
    val parameterizedSupertypes: Map<BoundBaseType, RootResolvedTypeReference>,
) {
    companion object {
        val EMPTY = PartialPreprocessedInheritanceTree(emptyMap())

        fun ofDirectSupertype(supertype: RootResolvedTypeReference): PartialPreprocessedInheritanceTree {
            if (supertype.baseType == supertype.context.swCtx.any) {
                return EMPTY
            }

            return PartialPreprocessedInheritanceTree(mapOf(supertype.baseType to supertype))
        }

        fun merge(
            partialTrees: Iterable<PartialPreprocessedInheritanceTree>,
            detectedCycles: Set<BoundSupertypeDeclaration>,
        ): PreprocessedInheritanceTree {
            val mergedParameterizedSupertypes = IdentityHashMap<BoundBaseType, RootResolvedTypeReference>()
            val inconsistentBindings = mutableMapOf<Pair<BoundBaseType, BoundTypeParameter>, MutableSet<BoundTypeArgument>>()
            for (partialTree in partialTrees) {
                for ((baseType, parameterized) in partialTree.parameterizedSupertypes) {
                    val existingParameterizedSupertype = mergedParameterizedSupertypes[baseType]
                    if (existingParameterizedSupertype != null) {
                        assert(existingParameterizedSupertype.baseType == baseType)
                        assert(existingParameterizedSupertype.arguments?.size == parameterized.arguments?.size)
                        if (existingParameterizedSupertype.arguments != null) {
                            zip(existingParameterizedSupertype.arguments, parameterized.arguments!!, existingParameterizedSupertype.baseType.typeParameters!!)
                                .filter { (existingArg, refArg, _) -> existingArg != refArg }
                                .forEach { (existingArg, refArg, param) ->
                                    val inconsistentArgs = inconsistentBindings.computeIfAbsent(Pair(existingParameterizedSupertype.baseType, param)) { mutableSetOf() }
                                    inconsistentArgs.add(refArg)
                                    inconsistentArgs.add(existingArg)
                                }
                        }
                    } else {
                        mergedParameterizedSupertypes[baseType] = parameterized
                    }
                }
            }

            return PreprocessedInheritanceTree(mergedParameterizedSupertypes, inconsistentBindings, detectedCycles)
        }
    }
}

class PreprocessedInheritanceTree(
    val parameterizedSupertypes: Map<BoundBaseType, RootResolvedTypeReference>,
    val inconsistentBindings: Map<Pair<BoundBaseType, BoundTypeParameter>, Set<BoundTypeArgument>>,
    val cycles: Set<BoundSupertypeDeclaration>,
) {
    /**
     * When a subtype inherits this [compiler.binding.type.PreprocessedInheritanceTree] from one of its supertypes,
     * this method translates the information for the subtype.
     */
    fun translateForSubtype(supertypeDeclaration: RootResolvedTypeReference): PartialPreprocessedInheritanceTree {
        return PartialPreprocessedInheritanceTree(
            parameterizedSupertypes.mapValues { (_, supertype) -> supertype.instantiateAllParameters(supertypeDeclaration.inherentTypeBindings) },
        )
    }
}