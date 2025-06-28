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
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundDeclaredBaseTypeMemberFunction
import compiler.binding.basetype.InheritedBoundMemberFunction
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.lexer.Keyword
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName

interface BoundFunction : SemanticallyAnalyzable, DefinitionWithVisibility {
    val context: CTContext
    val declaredAt: Span

    /**
     * The type of the receiver. Is null if the declared function has no receiver or if the declared receiver type
     * could not be resolved. See [declaresReceiver] to resolve the ambiguity.
     *
     * Available after [semanticAnalysisPhase1].
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
     * The side-effect category of this function, strictly as derived from [attributes].
     */
    val purity: Purity get() = attributes.purity

    /**
     * Is derived solely from [attributes] and [returnType]
     */
    val throwBehavior: SideEffectPrediction?
        get() = when {
            attributes.isDeclaredNothrow -> SideEffectPrediction.NEVER
            returnType != null && returnType!!.isNonNullableNothing -> SideEffectPrediction.GUARANTEED
            else -> SideEffectPrediction.POSSIBLY
        }

    val parameters: BoundParameterList

    val parameterTypes: List<BoundTypeReference?>
        get() = parameters.parameters.map { it.typeAtDeclarationTime }

    val returnType: BoundTypeReference?

    val canonicalName: CanonicalElementName.Function

    override fun toStringForErrorMessage() = "function $name"

    fun toBackendIr(): IrFunction

    enum class Purity(val keyword: Keyword) {
        PURE(Keyword.PURE),
        READONLY(Keyword.READONLY),
        MODIFYING(Keyword.MUTABLE),
        ;

        /**
         * @return whether [other] allows the same set or a subset of the side effects allowed by `this`.
         */
        fun contains(other: Purity): Boolean = when(this) {
            PURE -> other == PURE
            READONLY -> other == PURE || other == READONLY
            MODIFYING -> true
        }

        override fun toString() = name.lowercase()
    }
}

interface BoundMemberFunction : BoundFunction {
    val declaration: FunctionDeclaration

    /**
     * the [BoundBaseType] that declared this function. If `interface A` declares function `foo`
     * and interface `B` extends `A` without overriding `foo`, [declaredOnType] for `B::foo` will be `A`.
     */
    val declaredOnType: BoundBaseType

    /**
     * the [BoundBaseType] that owns this function. If `interface A` declares function `foo`
     * and interface `B` extends `A` without overriding `foo`, [ownerBaseType] for `B::foo` will be `B`.
     */
    val ownerBaseType: BoundBaseType

    /**
     * Whether this member function supports dynamic dispatch and whether it can be inherited from subtypes.
     * `null` if that cannot be determined (e.g. type error in the declared receiver).
     * Available after [semanticAnalysisPhase1].
     */
    val isVirtual: Boolean?

    val isAbstract: Boolean

    /**
     * Becomes meaningful during [semanticAnalysisPhase3].
     */
    val overrides: Set<InheritedBoundMemberFunction>?

    /**
     * A root is the function found by repeatedly following [overrides] until you hit a function that doesn't override
     * anything (= is original).
     *
     * **becomes available at the same time as [overrides].**
     */
    val roots: Set<BoundDeclaredBaseTypeMemberFunction>

    override fun toBackendIr(): IrMemberFunction
}