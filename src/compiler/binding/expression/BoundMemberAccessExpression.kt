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

package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.MemberAccessExpression
import compiler.binding.BoundExecutable
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.binding.type.ResolvedTypeReference
import compiler.binding.type.TypeUnification
import compiler.reportings.Reporting

class BoundMemberAccessExpression(
    override val context: CTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val isNullSafeAccess: Boolean,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    /**
     * The type of this expression. Is null before semantic anylsis phase 2 is finished; afterwards is null if the
     * type could not be determined or [memberName] denotes a function.
     */
    override var type: ResolvedTypeReference? = null
        private set

    private var member: ObjectMember? = null

    override val isGuaranteedToThrow = false // member accessor CAN throw, but must not ALWAYS do so

    override fun semanticAnalysisPhase1() = valueExpression.semanticAnalysisPhase1()
    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(valueExpression.semanticAnalysisPhase2())

        valueExpression.type?.let { valueType ->
            if (valueType.isNullable && !isNullSafeAccess) {
                reportings.add(Reporting.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
                // TODO: set the type of this expression nullable
            }
            else if (!valueType.isNullable && isNullSafeAccess) {
                reportings.add(Reporting.superfluousSafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
            }

            valueType.findMemberVariable(memberName)?.let { member ->
                this.member = member
                this.type = member.type?.contextualize(valueType.inherentTypeBindings, TypeUnification::left)
            } ?: run {
                reportings.add(Reporting.unresolvableMemberVariable(this, valueType))
            }
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return valueExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return valueExpression.findWritesBeyond(boundary)
    }
}