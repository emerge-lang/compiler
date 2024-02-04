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
import compiler.ast.expression.IdentifierExpression
import compiler.ast.type.TypeReference
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.UnresolvedType
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableReferenceExpression

class BoundIdentifierExpression(
    override val context: CTContext,
    override val declaration: IdentifierExpression
) : BoundExpression<IdentifierExpression> {
    val identifier: String = declaration.identifier.value

    override val type: BoundTypeReference?
        get() = when(val localReferral = referral) {
            is ReferringVariable -> localReferral.variable.type
            is ReferringType -> localReferral.reference
            null -> null
        }

    var referral: Referral? = null
        private set

    override var isGuaranteedToThrow = false

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // attempt variable
        val variable = context.resolveVariable(identifier)

        if (variable != null) {
            referral = ReferringVariable(variable)
        } else {
            val type: BoundTypeReference? = context.resolveType(
                TypeReference(declaration.identifier)
            ).takeUnless { it is UnresolvedType }

            if (type == null) {
                reportings.add(Reporting.undefinedIdentifier(declaration))
            } else {
                referral = ReferringType(type)
            }
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        if (type == null) {
            (referral as? ReferringVariable)?.variable?.semanticAnalysisPhase2()
        }

        return emptySet()
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return referral?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        // this does not write by itself; writs are done by other statements
        return emptySet()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do. identifiers must always be unambiguous so there is no use for this information
    }

    sealed interface Referral {
        fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>>
    }
    inner class ReferringVariable(val variable: BoundVariable) : Referral {
        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
            return if (context.containsWithinBoundary(variable, boundary)) {
                emptySet()
            } else {
                setOf(this@BoundIdentifierExpression)
            }
        }
    }
    inner class ReferringType(val reference: BoundTypeReference) : Referral {
        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
            // TODO is reading type information of types declared outside the boundary considered impure?
            return emptySet()
        }
    }

    private val _backendIr by lazy {
        (referral as? ReferringVariable)?.let { referral ->
            IrVariableReferenceExpressionImpl(referral.variable.backendIrDeclaration)
        } ?: TODO("implement type references")
    }

    override fun toBackendIr(): IrExpression = _backendIr
}

private class IrVariableReferenceExpressionImpl(
    override val variable: IrVariableDeclaration,
) : IrVariableReferenceExpression