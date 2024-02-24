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

import compiler.ast.expression.IdentifierExpression
import compiler.ast.type.TypeReference
import compiler.binding.BoundStatement
import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.UnresolvedType
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

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

        return reportings + (referral?.semanticAnalysisPhase1() ?: emptySet())
    }

    override fun markEvaluationResultUsed() {
        referral?.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        if (type == null) {
            (referral as? ReferringVariable)?.variable?.semanticAnalysisPhase2()?.let(reportings::addAll)
        }

        referral?.semanticAnalysisPhase2()?.let(reportings::addAll)

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return referral?.semanticAnalysisPhase3() ?: emptySet()
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return referral?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        // this does not write by itself; writs are done by other statements
        return emptySet()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do. identifiers must always be unambiguous so there is no use for this information
    }

    sealed interface Referral : SemanticallyAnalyzable {
        override fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()
        override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()
        override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()
        fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>>
        fun markEvaluationResultUsed()
    }
    inner class ReferringVariable(val variable: BoundVariable) : Referral {
        private var usageContext = VariableUsageContext.WRITE

        override fun markEvaluationResultUsed() {
            usageContext = VariableUsageContext.READ
        }

        override fun semanticAnalysisPhase3(): Collection<Reporting> {
            if (usageContext.requiresInitialization && !variable.isInitializedInContext(context)) {
                return setOf(Reporting.useOfUninitializedVariable(variable, this@BoundIdentifierExpression))
            }

            return emptySet()
        }

        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
            return if (context.containsWithinBoundary(variable, boundary)) {
                emptySet()
            } else {
                setOf(this@BoundIdentifierExpression)
            }
        }
    }
    inner class ReferringType(val reference: BoundTypeReference) : Referral {
        override fun markEvaluationResultUsed() {

        }

        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
            // TODO is reading type information of types declared outside the boundary considered impure?
            return emptySet()
        }
    }

    private val _backendIr by lazy {
        (referral as? ReferringVariable)?.let { referral ->
            IrVariableAccessExpressionImpl(
                referral.variable.backendIrDeclaration,
            )
        } ?: TODO("implement type references")
    }

    override fun toBackendIrExpression(): IrExpression = _backendIr

    private enum class VariableUsageContext(val requiresInitialization: Boolean) {
        READ(true),
        WRITE(false),
    }
}

internal class IrVariableAccessExpressionImpl(
    override val variable: IrVariableDeclaration,
) : IrVariableAccessExpression