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

package compiler.binding.classdef

import compiler.ast.ClassMemberDeclaration
import compiler.ast.ClassMemberVariableDeclaration
import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundElement
import compiler.binding.BoundVariable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundClassMemberVariable(
    override val context: ExecutionScopedCTContext,
    override val declaration: ClassMemberVariableDeclaration,
) : BoundElement<ClassMemberDeclaration>, BoundClassMember {
    override val name = declaration.name.value
    val isReAssignable = declaration.variableDeclaration.isReAssignable

    val isConstructorParameterInitialized = if (declaration.variableDeclaration.initializerExpression is IdentifierExpression) {
        declaration.variableDeclaration.initializerExpression.identifier.value == "init"
    } else {
        false
    }

    private val effectiveVariableDeclaration = if (!isConstructorParameterInitialized) declaration.variableDeclaration else {
        declaration.variableDeclaration.copy(initializerExpression = null)
    }
    private val boundEffectiveVariableDeclaration = effectiveVariableDeclaration.bindTo(context, BoundVariable.Kind.MEMBER_VARIABLE)

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
            TypeUseSite.InvariantUsage(declaration.variableDeclaration.type?.sourceLocation ?: declaration.declaredAt, this)
        } else {
            TypeUseSite.OutUsage(declaration.variableDeclaration.type?.sourceLocation ?: declaration.declaredAt, this)
        }
        reportings.addAll(type!!.validate(typeUseSite))
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

    override fun toStringForErrorMessage() = "member variable $name"

    private val _backendIr by lazy { IrClassMemberVariableImplVariable(name, type!!.toBackendIr()) }
    fun toBackendIr(): IrClass.MemberVariable = _backendIr
}

private class IrClassMemberVariableImplVariable(
    override val name: String,
    override val type: IrType,
) : IrClass.MemberVariable