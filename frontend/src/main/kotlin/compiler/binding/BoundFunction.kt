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

import compiler.binding.basetype.InheritedBoundMemberFunction
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction

interface BoundFunction : SemanticallyAnalyzable, DefinitionWithVisibility {
    val context: CTContext
    val declaredAt: SourceLocation

    /**
     * The type of the receiver. Is null if the declared function has no receiver or if the declared receiver type
     * could not be resolved. See [declaresReceiver] to resolve the ambiguity.
     */
    val receiverType: BoundTypeReference?

    /**
     * Whether this function declares a receiver. This allows disambiguating the case of a function without receiver
     * and a function with receiver whichs receiver type couldn't be resolved
     */
    val declaresReceiver: Boolean

    val name: String
    val attributes: BoundFunctionAttributeList

    override val visibility get()= attributes.visibility

    /**
     * All type parameters that are in play for this function signature, including ones inherited from context (e.g.
     * class member functions inherit type parameters from the class they are defined in).
     */
    val allTypeParameters: List<BoundTypeParameter>

    /**
     * The type parameters actually declared on this very function signature. In contrast to [allTypeParameters],
     * invocations can only specifiy [declaredTypeParameters] explicitly.
     */
    val declaredTypeParameters: List<BoundTypeParameter>

    /**
     * The side-effect category of this function. May give a stricter value than declared in [attributes]
     * if [semanticAnalysisPhase3] can proove that the code adheres to that stricter ruleset.
     * This value starts out with what can be derived from [attributes]. May change to be progressively more strict
     * as semantic analysis continues
     */
    val purity: Purity

    val isGuaranteedToThrow: Boolean?

    /** todo: remove for easier decoration using parameterTypes only */
    val parameters: BoundParameterList

    val parameterTypes: List<BoundTypeReference?>
        get() = parameters.parameters.map { it.typeAtDeclarationTime }

    val returnType: BoundTypeReference?

    val canonicalName: CanonicalElementName.Function

    override fun toStringForErrorMessage() = "function $name"

    fun toBackendIr(): IrFunction

    enum class Purity {
        PURE,
        READONLY,
        MODIFYING,
        ;

        /**
         * @return whether [other] allows the same set or a subset of the side effects allowed by `this`.
         */
        fun contains(other: Purity): Boolean = when(this) {
            PURE -> other == PURE
            READONLY -> other == PURE || other == READONLY
            MODIFYING -> true
        }
    }
}

interface BoundMemberFunction : BoundFunction {
    val declaredOnType: BaseType

    val isVirtual: Boolean

    val isAbstract: Boolean

    /**
     * Becomes meaningful during [semanticAnalysisPhase3]. Only set if [isVirtual]
     */
    val overrides: InheritedBoundMemberFunction?

    override fun toBackendIr(): IrMemberFunction
}