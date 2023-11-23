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
import compiler.ast.type.TypeReference
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

    /**
     * The result of the function dispatching. Is set (non null) after semantic analysis phase 2
     */
    var dispatchedFunction: BoundFunction? = null
        private set

    override val type: BaseTypeReference?
        get() = dispatchedFunction?.returnType

    override val isGuaranteedToThrow: Boolean?
        get() = dispatchedFunction?.isGuaranteedToThrow

    override fun semanticAnalysisPhase1(): Collection<Reporting> =
        onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            (receiverExpression?.semanticAnalysisPhase1()
                ?: emptySet()) + parameterExpressions.flatMap(BoundExpression<*>::semanticAnalysisPhase1)
        }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = mutableSetOf<Reporting>()

            receiverExpression?.semanticAnalysisPhase2()?.let(reportings::addAll)
            parameterExpressions.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }

            val parameterTypes = parameterExpressions.map(BoundExpression<*>::type)
            val resolvedConstructors = if (receiverExpression != null) null else context.resolveType(TypeReference(functionNameToken, false))?.constructors
            val resolvedFunctions = context.resolveFunction(functionNameToken.value)
            val receiverType = receiverExpression?.let { it.type ?: compiler.binding.type.Any.baseReference(context).nullable() }

            if (resolvedConstructors.isNullOrEmpty() && resolvedFunctions.isEmpty()) {
                reportings.add(Reporting.noMatchingFunctionOverload(functionNameToken, receiverType, parameterTypes, false))
                return@getResult reportings
            }

            if (resolvedConstructors != null) {
                val matchingConstructor = resolvedConstructors
                    .filterAndSortByMatchForInvocationTypes(null, parameterTypes)
                    .firstOrNull()

                if (matchingConstructor == null) {
                    reportings.add(Reporting.unresolvableConstructor(functionNameToken, parameterTypes, resolvedFunctions.isNotEmpty()))
                }

                dispatchedFunction = matchingConstructor
            } else {
                val matchingFunction = resolvedFunctions
                    .filterAndSortByMatchForInvocationTypes(receiverType, parameterTypes)
                    .firstOrNull()

                if (matchingFunction == null) {
                    reportings.add(Reporting.noMatchingFunctionOverload(functionNameToken, receiverType, parameterTypes, resolvedFunctions.isNotEmpty()))
                }

                dispatchedFunction = matchingFunction
            }

            dispatchedFunction?.semanticAnalysisPhase2()?.let(reportings::addAll)

            // TODO: determine type of invocation: static dispatch or dynamic dispatch

            return@getResult reportings
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