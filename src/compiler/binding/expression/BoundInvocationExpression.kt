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

import compiler.EarlyStackOverflowException
import compiler.OnceAction
import compiler.ast.Executable
import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.CyclicTypeInferenceException
import compiler.binding.context.CTContext
import compiler.binding.type.*
import compiler.lexer.IdentifierToken
import compiler.reportings.Reporting
import compiler.throwOnCycle

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

    override var type: ResolvedTypeReference? = null
        private set

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
            if (parameterTypes.any { it == null}) {
                // resolving the overload does not make sense if not all parameter types can be deducted
                // note that for erroneous type references, the parameter type will be a non-null UnresolvedType
                // so in that case we can still continue
                return@getResult reportings
            }
            parameterTypes as List<ResolvedTypeReference>

            val receiverType = receiverExpression?.type
            if (receiverExpression != null && receiverType == null) {
                // same goes for the receiver
                return@getResult reportings
            }

            val resolvedConstructors = if (receiverExpression != null) null else context.resolveBaseType(functionNameToken.value)?.constructors
            val resolvedFunctions = context.resolveFunction(functionNameToken.value)

            if (resolvedConstructors.isNullOrEmpty() && resolvedFunctions.isEmpty()) {
                reportings.add(Reporting.noMatchingFunctionOverload(functionNameToken, receiverType, parameterTypes, false))
                return@getResult reportings
            }

            val matchingFunctions: List<Pair<BoundFunction, TypeUnification>> = if (resolvedConstructors != null) {
                resolvedConstructors
                    .filterAndSortByMatchForInvocationTypes(null, parameterTypes)
            } else {
                resolvedFunctions
                    .filterAndSortByMatchForInvocationTypes(receiverType, parameterTypes)
            }

            matchingFunctions.firstOrNull()?.let { (matchingFunction, typeUnification) ->
                dispatchedFunction = matchingFunction
                try {
                    throwOnCycle(this) {
                        matchingFunction.semanticAnalysisPhase2()
                    }
                } catch (ex: EarlyStackOverflowException) {
                    throw CyclicTypeInferenceException()
                } catch (ex: CyclicTypeInferenceException) {
                    reportings.add(Reporting.typeDeductionError(
                        "Cannot infer return type of the call to function ${matchingFunction.name} because the inference is cyclic here. Specify the return type explicitly.",
                        declaration.sourceLocation,
                    ))
                }
                type = matchingFunction.returnType?.contextualize(typeUnification, TypeUnification::right)
                type?.validate(TypeUseSite.Irrelevant)?.let(reportings::addAll)
                if (resolvedConstructors != null && expectedReturnType != null) {
                    // we are calling a constructor. This is the only place in the entire language where one value
                    // can be legally assigned to both a mutable or an immutable reference, because at this stage
                    // there cannot be any other reference to that value
                    // this is solved by adjusting the return type of the constructor invocation according to the
                    // type needed by the larger context
                    type = type?.modifiedWith(expectedReturnType!!.mutability)
                }
            }

            if (matchingFunctions.isEmpty()) {
                if (resolvedConstructors != null) {
                    reportings.add(
                        Reporting.unresolvableConstructor(
                            functionNameToken,
                            parameterTypes,
                            resolvedFunctions.isNotEmpty(),
                        )
                    )
                } else {
                    reportings.add(
                        Reporting.noMatchingFunctionOverload(
                            functionNameToken,
                            receiverType,
                            parameterTypes,
                            resolvedFunctions.isNotEmpty(),
                        )
                    )
                }
            } else if (matchingFunctions.size > 1) {
                reportings.add(Reporting.ambiguousInvocation(this, matchingFunctions.map { it.first }))
            }

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

    private var expectedReturnType: ResolvedTypeReference? = null

    override fun setExpectedEvaluationResultType(type: ResolvedTypeReference) {
        onceAction.requireActionNotDone(OnceAction.SemanticAnalysisPhase2)
        expectedReturnType = type
    }
}


/**
 * Given the invocation types `receiverType` and `parameterTypes` of an invocation site
 * returns the functions matching the types sorted by matching quality to the given
 * types (see [ResolvedTypeReference.evaluateAssignabilityTo] and [ResolvedTypeReference.assignMatchQuality])
 *
 * In essence, this function is the overload resolution algorithm of the language.
 *
 * @return a list of matching functions, along with the resolved generics. Use the TypeUnification::right with the
 * returned function to determine the return type if that function were invoked.
 * The list is sorted by best-match first, worst-match last. However, if the return value has more than one element,
 * it has to be treated as an error because the invocation is ambiguous.
 */
private fun Iterable<BoundFunction>.filterAndSortByMatchForInvocationTypes(receiverType: ResolvedTypeReference?, parameterTypes: List<ResolvedTypeReference>): List<Pair<BoundFunction, TypeUnification>> {
    val leftSideTypes = listOfNotNull(receiverType) + parameterTypes
    return this
        .asSequence()
        // filter by (declared receiver)
        .filter { (receiverType != null) == it.declaresReceiver }
        // filter by incompatible number of parameters
        .filter { it.parameters.parameters.size == leftSideTypes.size }
        .mapNotNull { candidateFn ->
            if (candidateFn.parameterTypes.any { it == null }) {
                // types not fully resolve, don't consider
                return@mapNotNull null
            }
            @Suppress("UNCHECKED_CAST") // the check is right above
            val rightSideTypes = candidateFn.parameterTypes as List<ResolvedTypeReference>
            check(leftSideTypes.size == rightSideTypes.size)

            val unification = try {
                leftSideTypes
                    .zip(rightSideTypes)
                    .fold(TypeUnification.EMPTY) { unification, (lhsType, rhsType) -> lhsType.unify(rhsType, unification) }
            }
            catch (ex: TypesNotUnifiableException) {
                // type mismatch
                return@mapNotNull null
            }

            Pair(candidateFn, unification)
        }
        /*
        The following idea seems good after some thought:
        * A set of BaseTypes are "disjoint" if none of them is Any and their closestCommonSupertype is Any
          This means that two overloads of the same function that use disjoint types for the same parameter
          it is possible to disambiguate/choose the overload using that parameter only.
          This makes it impossible to overload a function for a more specific type. That is intentional, as it
          also removes the confusing behavior of runtime vs compile time overload resolution. Runtime overload
          resolution/multiple dispatch by-the-language (see groovy) seems unattractive. Its also easily implemented
          using a when { is } construct where needed. explicit is better than magic.
        * To be validated on the overloading declaration: for any set of overloads there must be at least one parameter
          whose types across all overloads are disjoint. That way, this parameter can disambiguate any call to that function
          instantly.
          This is aided by the fact that function parameter types must always be stated explicitly, so they are fully
          resolved after semanticAnalysisPhase1. That allows us to do overload resolution in phase 2 and thus infer types
          from overloaded invocations.
         */
        .sortedBy {
            TODO("overload resolution is not yet implemented. For now you can only have one function per name, sorry.")
        }
        .toList()
}