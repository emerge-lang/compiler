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

import compiler.InternalCompilerError
import compiler.ast.expression.NumericLiteralExpression
import compiler.binding.BoundStatement
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinByte
import compiler.binding.type.BuiltinInt
import compiler.binding.type.BuiltinLong
import compiler.binding.type.BuiltinNumber
import compiler.binding.type.BuiltinSignedWord
import compiler.binding.type.BuiltinType
import compiler.binding.type.BuiltinUByte
import compiler.binding.type.BuiltinUInt
import compiler.binding.type.BuiltinULong
import compiler.binding.type.BuiltinUnsignedWord
import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import java.math.BigDecimal
import java.math.BigInteger

/**
 * Should only be used when the numeric literal cannot be parsed correctly. Otherwise, use
 * [BoundIntegerLiteral] and [BoundFloatingPointLiteral].
 */
open class BoundNumericLiteral(
    override val context: ExecutionScopedCTContext,
    override val declaration: NumericLiteralExpression,
    private val reportings: Collection<Reporting>
) : BoundExpression<NumericLiteralExpression> {
    override val type: BoundTypeReference? = null // unknown

    override val isGuaranteedToThrow = false

    override fun semanticAnalysisPhase1() = reportings
    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()
    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> = emptySet()
    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> = emptySet()

    protected var expectedNumericType: BuiltinType? = null
    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        if (type !is RootResolvedTypeReference) {
            return
        }

        if (type.baseType !is BuiltinType) {
            return
        }

        if (BuiltinNumber !in type.baseType.superTypes) {
            return
        }

        expectedNumericType = type.baseType
    }

    override fun toBackendIrExpression(): IrExpression {
        throw InternalCompilerError("Numeric literal not completely recognized (int vs floating point)")
    }
}

class BoundIntegerLiteral(
    context: ExecutionScopedCTContext,
    declaration: NumericLiteralExpression,
    val integer: BigInteger,
    reportings: Collection<Reporting>
) : BoundNumericLiteral(context, declaration, reportings) {
    override var type = BuiltinInt.baseReference

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        if (expectedNumericType == null) {
            if (integer !in BuiltinInt.MIN .. BuiltinInt.MAX) {
                reportings.add(Reporting.integerLiteralOutOfRange(
                    declaration, BuiltinInt, BuiltinInt.MIN .. BuiltinInt.MAX
                ))
            }
            return reportings
        }

        expectedNumericType?.let { expectedType ->
            val range: ClosedRange<BigInteger> = when (expectedType) {
                BuiltinByte -> BuiltinByte.MIN .. BuiltinByte.MAX
                BuiltinUByte -> BuiltinUByte.MIN .. BuiltinUByte.MAX
                BuiltinInt -> BuiltinInt.MIN .. BuiltinInt.MAX
                BuiltinUInt -> BuiltinUInt.MIN .. BuiltinUInt.MAX
                BuiltinLong -> BuiltinLong.MIN .. BuiltinLong.MAX
                BuiltinULong -> BuiltinULong.MIN .. BuiltinULong.MAX
                BuiltinSignedWord -> BuiltinSignedWord.SAFE_MIN .. BuiltinSignedWord.SAFE_MAX
                BuiltinUnsignedWord -> BuiltinUnsignedWord.SAFE_MIN .. BuiltinUnsignedWord.SAFE_MAX
                else -> return reportings
            }

            // even if the literal doesn't fit into the expected type, setting this makes sense: it makes a
            // possible cannot-be-assigned error go away. there already is an error for the out-of-range literal,
            // no need for a second reporting on the same error
            type = expectedType.baseReference
            if (integer !in range) {
                reportings.add(Reporting.integerLiteralOutOfRange(declaration, expectedType, range))
            }
        }

        return reportings
    }

    override fun toBackendIrExpression(): IrExpression {
        return IrIntegerLiteralExpressionImpl(
            integer,
            type.toBackendIr(),
        )
    }
}

class BoundFloatingPointLiteral(
    context: ExecutionScopedCTContext,
    declaration: NumericLiteralExpression,
    val float: BigDecimal,
    reportings: Collection<Reporting>
) : BoundNumericLiteral(context, declaration, reportings) {
    override val type = compiler.binding.type.BuiltinFloat.baseReference

    override fun toBackendIrExpression(): IrExpression {
        TODO()
    }
}

internal class IrIntegerLiteralExpressionImpl(
    override val value: BigInteger,
    override val evaluatesTo: IrType,
) : IrIntegerLiteralExpression