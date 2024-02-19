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

import compiler.ast.expression.BooleanLiteralExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinBoolean
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundBooleanLiteralExpression(
    override val context: CTContext,
    override val declaration: BooleanLiteralExpression,
    val value: Boolean
) : BoundExpression<BooleanLiteralExpression> {
    override val type: BoundTypeReference = BuiltinBoolean.baseReference

    override val isGuaranteedToThrow: Boolean = false

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do: this expression can only ever have one type
    }

    override fun toBackendIr(): IrExpression {
        return IrBooleanLiteralExpressionImpl(type.toBackendIr(), value)
    }
}

private class IrBooleanLiteralExpressionImpl(
    override val evaluatesTo: IrType,
    override val value: Boolean,
) : IrBooleanLiteralExpression