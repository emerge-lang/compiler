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

import compiler.ast.type.FunctionModifier
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.lexer.SourceLocation
import compiler.ast.type.TypeMutability

abstract class BoundFunction : SemanticallyAnalyzable {
    abstract val context: CTContext
    abstract val declaredAt: SourceLocation

    /**
     * The type of the receiver. Is null if the declared function has no receiver or if the declared receiver type
     * could not be resolved. See [declaresReceiver] to resolve the ambiguity.
     */
    abstract val receiverType: BoundTypeReference?

    /**
     * Whether this function declares a receiver. This allows disambiguating the case of a function without receiver
     * and a function with receiver whichs receiver type couldn't be resolved
     */
    abstract val declaresReceiver: Boolean

    abstract val name: String
    abstract val modifiers: Set<FunctionModifier>

    abstract val typeParameters: List<BoundTypeParameter>

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

    val parameterTypes: List<BoundTypeReference?>
        get() = parameters.parameters.map { it.type }

    abstract val returnType: BoundTypeReference?

    /**
     * If true, this function returns a value with no references to it. This is only possible for constructors.
     * Knowing this allows assigning that value to all [TypeMutability]s, something impossible otherwise.
     */
    open val returnsExclusiveValue: Boolean = false

    val fullyQualifiedName: String
        get() = context.sourceFile.packageName.joinToString(".") + "." + name
}