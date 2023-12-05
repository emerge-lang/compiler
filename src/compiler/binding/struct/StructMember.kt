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

package compiler.binding.struct

import compiler.ast.Executable
import compiler.ast.struct.StructMemberDeclaration
import compiler.binding.BoundElement
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.ResolvedTypeReference
import compiler.reportings.Reporting
import compiler.reportings.StructMemberDefaultValueNotAssignableReporting

class StructMember(
    override val context: StructContext,
    override val declaration: StructMemberDeclaration,
    val defaultValue: BoundExpression<*>?
) : BoundElement<StructMemberDeclaration> {
    val name: String = declaration.name.value

    /**
     * The type of the member; is null if not yet determined or if it cannot be determined.
     */
    var type: ResolvedTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        type = declaration.type.resolveWithin(context)
        reportings.addAll(type!!.validate())

        if (defaultValue != null) {
            reportings.addAll(defaultValue.semanticAnalysisPhase1())
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return defaultValue?.semanticAnalysisPhase2() ?: emptySet()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (defaultValue != null) {
            reportings.addAll(defaultValue.semanticAnalysisPhase3())

            val defaultValueType = defaultValue.type
            if (defaultValueType != null && type != null) {
                defaultValueType.evaluateAssignabilityTo(type!!, this.declaration.declaredAt)
                    ?.let {
                        reportings.add(StructMemberDefaultValueNotAssignableReporting(this, it))
                    }
            }
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return defaultValue?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return defaultValue?.findWritesBeyond(boundary) ?: emptySet()
    }
}