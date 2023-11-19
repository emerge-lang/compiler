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

import compiler.OnceAction
import compiler.ast.Executable
import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken
import compiler.reportings.Reporting

class BoundInvocationExpression(
    override val context: CTContext,
    override val declaration: InvocationExpression,
    /** The receiver expression; is null if not specified in the source */
    val receiverExpression: BoundExpression<*>?,
    val functionNameToken: IdentifierToken,
    val parameterExpressions: List<BoundExpression<*>>
) : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression> {

    private val onceAction = OnceAction()

    override var type: BaseTypeReference? = null
        private set

    /**
     * The result of the function dispatching. Is set (non null) after semantic analysis phase 2
     */
    var dispatchedFunction: BoundFunction? = null
        private set

    override var isGuaranteedToThrow: Boolean? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> =
        onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            (receiverExpression?.semanticAnalysisPhase1()
                ?: emptySet()) + parameterExpressions.flatMap(BoundExpression<*>::semanticAnalysisPhase1)
        }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = mutableSetOf<Reporting>()

            if (receiverExpression != null) reportings.addAll(receiverExpression.semanticAnalysisPhase2())
            parameterExpressions.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }

            // determine the function to be invoked
            semanticPhase2_determineFunction().firstOrNull()?.let { function ->
                reportings.addAll(function.semanticAnalysisPhase2())
                dispatchedFunction = function
                type = function.returnType
                isGuaranteedToThrow = function.code?.isGuaranteedToThrow
            }
            ?: reportings.add(Reporting.unresolvableFunction(this))

            // TODO: determine type of invocation: static dispatch or dynamic dispatch

            return@getResult reportings
        }
    }

    /**
     * Attempts to resolve all candidates for the invocation. If the receiver type cannot be resolved, assumes `Any?`
     */
    private fun semanticPhase2_determineFunction(): List<BoundFunction> {
        if (receiverExpression == null) {
            return context.resolveFunction(functionNameToken.value)
                    .filter { it.receiverType == null }
                    .filterAndSortByMatchForInvocationTypes(null, parameterExpressions.map(BoundExpression<*>::type))
        } else {
            val receiverType = receiverExpression.type ?: compiler.binding.type.Any.baseReference(context).nullable()
            return context.resolveFunction(functionNameToken.value)
                .filterAndSortByMatchForInvocationTypes(
                    receiverType,
                    parameterExpressions.map { it.type }
                )
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = mutableSetOf<Reporting>()

            if (receiverExpression != null) {
                reportings += receiverExpression.semanticAnalysisPhase3()
            }

            reportings += parameterExpressions.flatMap { it.semanticAnalysisPhase3() }

            return@getResult reportings
        }
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        onceAction.requireActionDone(OnceAction.SemanticAnalysisPhase1)
        onceAction.requireActionDone(OnceAction.SemanticAnalysisPhase2)

        val byReceiver = receiverExpression?.findReadsBeyond(boundary) ?: emptySet()
        val byParameters = parameterExpressions.flatMap { it.findReadsBeyond(boundary) }

        if (dispatchedFunction != null) {
            if (dispatchedFunction!!.isPure == null) {
                dispatchedFunction!!.semanticAnalysisPhase3()
            }
        }

        val dispatchedFunctionIsPure = dispatchedFunction?.isPure ?: true
        val bySelf = if (dispatchedFunctionIsPure) emptySet() else setOf(this)

        return byReceiver + byParameters + bySelf
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        onceAction.requireActionDone(OnceAction.SemanticAnalysisPhase1)
        onceAction.requireActionDone(OnceAction.SemanticAnalysisPhase2)

        val byReceiver = receiverExpression?.findWritesBeyond(boundary) ?: emptySet()
        val byParameters = parameterExpressions.flatMap { it.findWritesBeyond(boundary) }

        if (dispatchedFunction != null) {
            if (dispatchedFunction!!.isReadonly == null) {
                dispatchedFunction!!.semanticAnalysisPhase3()
            }
        }

        val thisExpressionIsReadonly = dispatchedFunction?.isReadonly ?: true
        val bySelf: Collection<BoundExecutable<Executable<*>>> = if (thisExpressionIsReadonly) emptySet() else setOf(this)

        return byReceiver + byParameters + bySelf
    }
}
