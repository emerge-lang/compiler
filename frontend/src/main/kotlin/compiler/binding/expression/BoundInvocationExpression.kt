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
import compiler.binding.type.*
import compiler.handleCyclicInvocation
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression

class BoundInvocationExpression(
    override val context: CTContext,
    override val declaration: InvocationExpression,
    /** The receiver expression; is null if not specified in the source */
    val receiverExpression: BoundExpression<*>?,
    val functionNameToken: IdentifierToken,
    val valueArguments: List<BoundExpression<*>>
) : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression> {

    private val onceAction = OnceAction()

    /**
     * The result of the function dispatching. Is set (non null) after semantic analysis phase 2
     */
    var dispatchedFunction: BoundFunction? = null
        private set

    override var type: BoundTypeReference? = null
        private set

    lateinit var typeArguments: List<BoundTypeArgument>
        private set

    override val isGuaranteedToThrow: Boolean?
        get() = dispatchedFunction?.isGuaranteedToThrow

    override fun semanticAnalysisPhase1(): Collection<Reporting> =
        onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()
            receiverExpression?.semanticAnalysisPhase1()?.let(reportings::addAll)
            valueArguments.map(BoundExpression<*>::semanticAnalysisPhase1).forEach(reportings::addAll)
            typeArguments = declaration.typeArguments.map(context::resolveType)
            reportings
        }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            receiverExpression?.markEvaluationResultUsed()
            valueArguments.forEach { it.markEvaluationResultUsed() }

            val reportings = mutableSetOf<Reporting>()

            receiverExpression?.semanticAnalysisPhase2()?.let(reportings::addAll)
            typeArguments.forEach { reportings.addAll(it.validate(TypeUseSite.Irrelevant)) }
            valueArguments.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }

            val chosenOverload = selectOverload(reportings) ?: return@getResult reportings

            dispatchedFunction = chosenOverload.candidate
            handleCyclicInvocation(
                context = this,
                action = { chosenOverload.candidate.semanticAnalysisPhase2() },
                onCycle = {
                    reportings.add(Reporting.typeDeductionError(
                        "Cannot infer return type of the call to function ${functionNameToken.value} because the inference is cyclic here. Specify the return type explicitly.",
                        declaration.sourceLocation,
                    ))
                }
            )

            type = chosenOverload.returnType
            if (chosenOverload.candidate.returnsExclusiveValue && expectedReturnType != null) {
                // this is solved by adjusting the return type of the constructor invocation according to the
                // type needed by the larger context
                type = type?.withMutability(expectedReturnType!!.mutability)
            }

            return@getResult reportings
        }
    }

    /**
     * Selects one of the given overloads, including ones that are not a legal match if there are no legal alternatives.
     * Also performs the following checks and reports accordingly:
     * * absolutely no candidate available to evaluate
     * * of the evaluated constructors or functions, none match
     * * if there is only one overload to pick from, forwards any reportings from evaluating that candidate
     */
    private fun selectOverload(reportings: MutableCollection<in Reporting>): OverloadCandidateEvaluation? {
        if (valueArguments.any { it.type == null}) {
            // resolving the overload does not make sense if not all parameter types can be deducted
            // note that for erroneous type references, the parameter type will be a non-null UnresolvedType
            // so in that case we can still continue
            return null
        }

        if (receiverExpression != null && receiverExpression.type == null) {
            // same goes for the receiver
            return null
        }

        val candidateConstructors = if (receiverExpression != null) null else context.resolveBaseType(functionNameToken.value)?.constructors
        val candidateFunctions = context.resolveFunction(functionNameToken.value)

        if (candidateConstructors.isNullOrEmpty() && candidateFunctions.isEmpty()) {
            reportings.add(Reporting.noMatchingFunctionOverload(functionNameToken, receiverExpression?.type, valueArguments, false))
            return null
        }

        val evaluations: List<OverloadCandidateEvaluation> = if (candidateConstructors != null) {
            candidateConstructors
                .filterAndSortByMatchForInvocationTypes(null, valueArguments, typeArguments, expectedReturnType)
        } else {
            candidateFunctions
                .filterAndSortByMatchForInvocationTypes(receiverExpression, valueArguments, typeArguments, expectedReturnType)
        }

        if (evaluations.isEmpty()) {
            // TODO: pass on the mismatch reason for all candidates?
            if (candidateConstructors != null) {
                reportings.add(
                    Reporting.unresolvableConstructor(
                        functionNameToken,
                        valueArguments,
                        candidateFunctions.isNotEmpty(),
                    )
                )
            } else {
                reportings.add(
                    Reporting.noMatchingFunctionOverload(
                        functionNameToken,
                        receiverExpression?.type,
                        valueArguments,
                        candidateFunctions.isNotEmpty(),
                    )
                )
            }
        }

        val legalMatches = evaluations.filter { !it.hasErrors }
        if (legalMatches.size > 1) {
            reportings.add(Reporting.ambiguousInvocation(this, evaluations.map { it.candidate }))
        }
        if (legalMatches.isEmpty()) {
            // if there is only a single candidate, the errors found in validating are 100% applicable to be shown to the user
            evaluations
                .singleOrNull()
                ?.unification
                ?.reportings
                ?.let(reportings::addAll)
        }

        return legalMatches.firstOrNull() ?: evaluations.firstOrNull()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = mutableSetOf<Reporting>()

            if (receiverExpression != null) {
                reportings += receiverExpression.semanticAnalysisPhase3()
            }

            reportings += valueArguments.flatMap { it.semanticAnalysisPhase3() }

            return@getResult reportings
        }
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        onceAction.requireActionDone(OnceAction.SemanticAnalysisPhase1)
        onceAction.requireActionDone(OnceAction.SemanticAnalysisPhase2)

        val byReceiver = receiverExpression?.findReadsBeyond(boundary) ?: emptySet()
        val byParameters = valueArguments.flatMap { it.findReadsBeyond(boundary) }

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
        val byParameters = valueArguments.flatMap { it.findWritesBeyond(boundary) }

        if (dispatchedFunction != null) {
            if (dispatchedFunction!!.isReadonly == null) {
                dispatchedFunction!!.semanticAnalysisPhase3()
            }
        }

        val thisExpressionIsReadonly = dispatchedFunction?.isReadonly ?: true
        val bySelf: Collection<BoundExecutable<Executable<*>>> = if (thisExpressionIsReadonly) emptySet() else setOf(this)

        return byReceiver + byParameters + bySelf
    }

    private var expectedReturnType: BoundTypeReference? = null

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        onceAction.requireActionNotDone(OnceAction.SemanticAnalysisPhase2)
        expectedReturnType = type
    }

    override fun toBackendIr(): IrExpression {
        return IrStaticDispatchFunctionInvocationImpl(this)
    }
}


/**
 * Given the invocation types `receiverType` and `parameterTypes` of an invocation site
 * returns the functions matching the types sorted by matching quality to the given
 * types (see [BoundTypeReference.evaluateAssignabilityTo] and [BoundTypeReference.assignMatchQuality])
 *
 * In essence, this function is the overload resolution algorithm of Emerge.
 *
 * @return a list of matching functions, along with the resolved generics. Use the TypeUnification::right with the
 * returned function to determine the return type if that function were invoked.
 * The list is sorted by best-match first, worst-match last. However, if the return value has more than one element,
 * it has to be treated as an error because the invocation is ambiguous.
 */
private fun Iterable<BoundFunction>.filterAndSortByMatchForInvocationTypes(
    receiver: BoundExpression<*>?,
    valueArguments: List<BoundExpression<*>>,
    typeArguments: List<BoundTypeArgument>,
    expectedReturnType: BoundTypeReference?,
): List<OverloadCandidateEvaluation> {
    check((receiver != null) xor (receiver?.type == null))
    val receiverType = receiver?.type
    val argumentsIncludingReceiver = listOfNotNull(receiver) + valueArguments
    return this
        .asSequence()
        // filter by (declared receiver)
        .filter { candidateFn ->
            if ((receiverType != null) != candidateFn.declaresReceiver) {
                return@filter false
            }

            if (receiverType == null) {
                return@filter true
            }

            val receiverTypeUnification = candidateFn.receiverType!!.withTypeVariables(candidateFn.typeParameters).unify(receiverType, SourceLocation.UNKNOWN, TypeUnification.EMPTY)
            receiverTypeUnification.reportings.none { it.level >= Reporting.Level.ERROR }
        }
        // filter by incompatible number of parameters
        .filter { it.parameters.parameters.size == argumentsIncludingReceiver.size }
        .mapNotNull { candidateFn ->
            if (candidateFn.parameterTypes.any { it == null }) {
                // types not fully resolve, don't consider
                return@mapNotNull null
            }

            // TODO: source location
            val returnTypeWithVariables = candidateFn.returnType?.withTypeVariables(candidateFn.typeParameters)
            var unification = TypeUnification.fromExplicit(candidateFn.typeParameters, typeArguments, SourceLocation.UNKNOWN, allowZeroTypeArguments = true)
            if (returnTypeWithVariables != null) {
                if (expectedReturnType != null) {
                    unification = unification.doWithIgnoringReportings { obliviousUnification ->
                        expectedReturnType.unify(returnTypeWithVariables, SourceLocation.UNKNOWN, obliviousUnification)
                    }
                }
            }

            @Suppress("UNCHECKED_CAST") // the check is right above
            val rightSideTypes = (candidateFn.parameterTypes as List<BoundTypeReference>)
                .map { it.withTypeVariables(candidateFn.typeParameters) }
            check(rightSideTypes.size == argumentsIncludingReceiver.size)

            unification = argumentsIncludingReceiver
                .zip(rightSideTypes)
                .fold(unification) { unification, (argument, parameterType) ->
                    parameterType.unify(argument.type!!, argument.declaration.sourceLocation, unification)
                }

            OverloadCandidateEvaluation(
                candidateFn,
                unification,
                returnTypeWithVariables?.instantiateFreeVariables(unification),
            )
        }
        /*
        The following idea seems good after some thought:
        * A set of Types are "disjoint" if there is no value other than Nothing that can be assigned to
          all types. Put differently: if their closestCommonSupertype does not equal any of the input types

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
        * lambda literals with untyped parameters cannot contribute to overload resolution because they can change
          their output based on the input, making the whole unification complex an order of magnitude more complicated.
          It should still be possible for function types to be disambiguators (see above). In that case there should be
          a warning, though, saying that the disambiguation on a function type prevents users from passing a lambda
          literal argument to that function.
        * optional parameters: once they are added, the overload validation has to consider them, too. In that case
          the disjoint parameter constraint only applies within the set of overload that has the same amount of
          required parameters.
         */
        .sortedBy {
            TODO("overload resolution is not yet implemented. For now you can only have one function per name, sorry.")
        }
        .toList()
}

private data class OverloadCandidateEvaluation(
    val candidate: BoundFunction,
    val unification: TypeUnification,
    val returnType: BoundTypeReference?,
) {
    val hasErrors = unification.reportings.any { it.level >= Reporting.Level.ERROR }
}

private class IrStaticDispatchFunctionInvocationImpl(
    private val invocation: BoundInvocationExpression,
) : IrStaticDispatchFunctionInvocationExpression {
    private val irReturnType by lazy { invocation.type!!.toBackendIr() }
    private val irFunction by lazy { invocation.dispatchedFunction!!.toBackendIr() }
    private val irArguments by lazy { (listOfNotNull(invocation.receiverExpression) + invocation.valueArguments).map { it.toBackendIr() } }

    override val evaluatesTo get() = irReturnType
    override val function get() = irFunction
    override val arguments get() = irArguments
}