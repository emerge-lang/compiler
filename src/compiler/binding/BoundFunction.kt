/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.ast.type.FunctionModifier
import compiler.binding.context.CTContext
import compiler.binding.type.Any
import compiler.binding.type.BaseTypeReference
import compiler.lexer.SourceLocation

abstract class BoundFunction : SemanticallyAnalyzable {
    abstract val context: CTContext
    abstract val declaredAt: SourceLocation

    /**
     * The type of the receiver. Is null if the declared function has no receiver or if the declared receiver type
     * could not be resolved. See [FunctionDeclaration.receiverType] to resolve the ambiguity.
     */
    abstract val receiverType: BaseTypeReference?

    abstract val name: String
    abstract val modifiers: Set<FunctionModifier>

    /**
     * Whether this function should be considered pure by other code using it. This is true if the function is
     * declared pure. If that is not the case the function is still considered pure if the declared
     * body behaves in a pure way.
     * This value is null if the purity was not yet determined; it must be non-null when semantic analysis is completed.
     * @see [BoundDeclaredFunction.isDeclaredPure]
     * @see [BoundDeclaredFunction.isEffectivelyPure]
     */
    abstract val isPure: Boolean?

    /**
     * Whether this function should be considered readonly by other code using it. This is true if the function is
     * declared readonly or pure. If that is not the case the function is still considered readonly if the declared
     * body behaves in a readonly way.
     * This value is null if the purity was not yet determined; it must be non-null when semantic analysis is completed.
     * @see [BoundDeclaredFunction.isDeclaredReadonly]
     * @see [BoundDeclaredFunction.isEffectivelyReadonly]
     */
    abstract val isReadonly: Boolean?

    abstract val isGuaranteedToThrow: Boolean?

    abstract val parameters: BoundParameterList

    val parameterTypes: List<BaseTypeReference?>
        get() = parameters.parameters.map { it.type }

    abstract val returnType: BaseTypeReference?

    val fullyQualifiedName: String
        get() = context.module.name.joinToString(".") + "." + name
}

/**
 * Given the invocation types `receiverType` and `parameterTypes` of an invocation site
 * returns the functions matching the types sorted by matching quality to the given
 * types (see [BaseTypeReference.isAssignableTo] and [BaseTypeReference.assignMatchQuality])
 *
 * In essence, this function is the function dispatching algorithm of the language.
 */
fun Iterable<BoundFunction>.filterAndSortByMatchForInvocationTypes(receiverType: BaseTypeReference?, parameterTypes: Iterable<BaseTypeReference?>): List<BoundFunction> =
    this
        // filter out the ones with incompatible receiver type
        .filter {
            // both null -> don't bother about the receiverType for now
            if (receiverType == null && it.receiverType == null) {
                return@filter true
            }
            // both must be non-null
            if (receiverType == null || it.receiverType == null) {
                return@filter false
            }

            return@filter receiverType.isAssignableTo(it.receiverType!!)
        }
        // filter by incompatible number of parameters
        .filter { it.parameters.parameters.size == parameterTypes.count() }
        // filter by incompatible parameters
        .filter { candidateFn ->
            parameterTypes.forEachIndexed { paramIndex, paramType ->
                val candidateParamType = candidateFn.parameterTypes[paramIndex] ?: Any.baseReference(candidateFn.context)
                if (paramType != null && !(paramType isAssignableTo candidateParamType)) {
                    return@filter false
                }
            }

            return@filter true
        }
        // now we can sort
        // by receiverType ASC, parameter... ASC
        .sortedWith(
            compareBy(
                // receiver type
                {
                    receiverType?.assignMatchQuality(it.receiverType!!) ?: 0
                },
                // parameters
                { candidateFn ->
                    var value: Int = 0
                    parameterTypes.forEachIndexed { paramIndex, paramType ->
                        value = paramType?.assignMatchQuality(candidateFn.parameterTypes[paramIndex] ?: Any.baseReference(candidateFn.context)) ?: 0
                        if (value != 0) return@forEachIndexed
                    }

                    value
                }
            )
        )
