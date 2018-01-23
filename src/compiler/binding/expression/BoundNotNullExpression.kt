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
import compiler.ast.expression.NotNullExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundNotNullExpression(
    override val context: CTContext,
    override val declaration: NotNullExpression,
    val nullableExpression: BoundExpression<*>
) : BoundExpression<NotNullExpression>, BoundExecutable<NotNullExpression> {
    // TODO: reporting on superfluous notnull when nullableExpression.type.nullable == false

    override var type: BaseTypeReference? = null
        private set

    override val isGuaranteedToThrow = false // this MAY throw, but its not guaranteed to

    override fun semanticAnalysisPhase1() = super<BoundExpression>.semanticAnalysisPhase1()
    override fun semanticAnalysisPhase2() = super<BoundExpression>.semanticAnalysisPhase2()
    override fun semanticAnalysisPhase3() = super<BoundExpression>.semanticAnalysisPhase3()

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return nullableExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> = emptySet()
}