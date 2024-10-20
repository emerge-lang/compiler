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

package compiler.binding.basetype

import compiler.ast.BaseTypeMemberDeclaration
import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.ast.expression.IdentifierExpression
import compiler.binding.DefinitionWithVisibility
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.lexer.Span
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundBaseTypeMemberVariable(
    val context: ExecutionScopedCTContext,
    val declaration: BaseTypeMemberVariableDeclaration,
    private val getTypeDef: () -> BoundBaseType,
) : BoundBaseTypeEntry<BaseTypeMemberDeclaration>, DefinitionWithVisibility {
    val name = declaration.name.value
    override val declaredAt = declaration.span
    val isReAssignable = declaration.variableDeclaration.isReAssignable

    val isConstructorParameterInitialized = if (declaration.variableDeclaration.initializerExpression is IdentifierExpression) {
        declaration.variableDeclaration.initializerExpression.identifier.value == "init"
    } else {
        false
    }

    private val effectiveVariableDeclaration = if (!isConstructorParameterInitialized) declaration.variableDeclaration else {
        declaration.variableDeclaration.copy(initializerExpression = null)
    }
    private val boundEffectiveVariableDeclaration = effectiveVariableDeclaration.bindToAsMemberVariable(context)

    override val visibility = boundEffectiveVariableDeclaration.visibility

    /**
     * The initial value for this member variable, or `null` if [isConstructorParameterInitialized]
     */
    val initializer: BoundExpression<*>? = boundEffectiveVariableDeclaration.initializerExpression

    val modifiedContext: ExecutionScopedCTContext get() = boundEffectiveVariableDeclaration.modifiedContext

    /**
     * The type of this member in the context of the hosting data structure. It still needs to
     * be [BoundTypeReference.instantiateAllParameters]-ed with the type of the variable used to access
     * the hosting data structure.
     *
     * Is null if not yet determined or if it cannot be determined.
     */
    val type: BoundTypeReference? get() = boundEffectiveVariableDeclaration.typeAtDeclarationTime

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(boundEffectiveVariableDeclaration.semanticAnalysisPhase1())
        reportings.addAll(visibility.validateOnElement(this))
        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = boundEffectiveVariableDeclaration.semanticAnalysisPhase2().toMutableList()
        val typeUseSite = if (declaration.variableDeclaration.isReAssignable) {
            TypeUseSite.InvariantUsage(declaration.variableDeclaration.type?.span ?: declaration.span, this)
        } else {
            TypeUseSite.OutUsage(declaration.variableDeclaration.type?.span ?: declaration.span, this)
        }
        type?.validate(typeUseSite)?.let(reportings::addAll)
        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(boundEffectiveVariableDeclaration.semanticAnalysisPhase3())

        if (boundEffectiveVariableDeclaration.initializerExpression != null) {
            reportings.addAll(Reporting.purityViolations(
                boundEffectiveVariableDeclaration.initializerExpression.findReadsBeyond(context),
                boundEffectiveVariableDeclaration.initializerExpression.findWritesBeyond(context),
                this,
            ))
        }

        return reportings
    }

    lateinit var field: BaseTypeField
        private set

    /**
     * Assures [field] is initialized. Must only be called after semantic analysis is successfully completed.
     */
    fun assureFieldAllocated() {
        if (!this::field.isInitialized) {
            field = getTypeDef().allocateField(this.type!!)
        }
    }

    override fun validateAccessFrom(location: Span): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "member variable $name"

    private val _backendIr by lazy {
        IrClassMemberVariableImpl(name, type!!.toBackendIr(), field.id)
    }
    fun toBackendIr(): IrClass.MemberVariable = _backendIr
}

private class IrClassMemberVariableImpl(
    override val name: String,
    override val type: IrType,
    private val fieldId: Int,
) : IrClass.MemberVariable {
    override val readStrategy = object : IrClass.MemberVariable.AccessStrategy.BareField {
        override val fieldId: Int = this@IrClassMemberVariableImpl.fieldId
    }
    override val writeStrategy = readStrategy
}