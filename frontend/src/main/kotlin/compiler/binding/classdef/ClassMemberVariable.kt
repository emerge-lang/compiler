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

import compiler.ast.classdef.ClassMemberDeclaration
import compiler.binding.BoundElement
import compiler.binding.ObjectMember
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.reportings.ClassMemberVariableDefaultValueNotAssignableReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class ClassMemberVariable(
    override val context: ClassContext,
    override val declaration: ClassMemberDeclaration,
    val defaultValue: BoundExpression<*>?
) : BoundElement<ClassMemberDeclaration>, ObjectMember {
    override val name = declaration.name.value
    override val isMutable = true

    /**
     * The type of the member; is null if not yet determined or if it cannot be determined.
     */
    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        type = context.resolveType(declaration.type)

        if (defaultValue != null) {
            reportings.addAll(defaultValue.semanticAnalysisPhase1())
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(type!!.validate(TypeUseSite.InvariantUsage(declaration.type.sourceLocation ?: declaration.declaredAt)))
        defaultValue?.semanticAnalysisPhase2()?.let(reportings::addAll)
        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (defaultValue != null) {
            reportings.addAll(defaultValue.semanticAnalysisPhase3())

            val defaultValueType = defaultValue.type
            if (defaultValueType != null && type != null) {
                defaultValueType.evaluateAssignabilityTo(type!!, this.declaration.declaredAt)
                    ?.let {
                        reportings.add(ClassMemberVariableDefaultValueNotAssignableReporting(this, it))
                    }
            }
        }

        return reportings
    }

    private val _backendIr by lazy { IrClassMemberVariableImplVariable(name, type!!.toBackendIr()) }
    fun toBackendIr(): IrClass.MemberVariable = _backendIr
}

private class IrClassMemberVariableImplVariable(
    override val name: String,
    override val type: IrType,
) : IrClass.MemberVariable