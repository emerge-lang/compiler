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

import compiler.ast.AstAnnotationSet
import compiler.ast.VariableDeclaration
import compiler.ast.expression.InvocationExpression
import compiler.ast.type.AstWildcardTypeArgument
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.*
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.InheritedBoundMemberFunction
import compiler.binding.context.*
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.context.effect.VariableTypeRefinement
import compiler.binding.expression.BoundExpression.ImplyingResult
import compiler.binding.expression.BoundInvocationExpression.CandidateFilter.Result
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.*
import compiler.binding.type.*
import compiler.diagnostic.*
import compiler.handleCyclicInvocation
import compiler.lexer.IdentifierToken
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import compiler.util.mapToBackendIrWithDebugLocations
import io.github.tmarsteel.emerge.backend.api.ir.*
import io.github.tmarsteel.emerge.common.EmergeConstants

class BoundInvocationExpression(
    /** the context after all [valueArguments] have been evaluated */
    override val context: ExecutionScopedCTContext,
    /** the context before any of the [valueArguments] is evaluated */
    contextBeforeInvocation: ExecutionScopedCTContext,
    override val declaration: InvocationExpression,
    /** The receiver expression; is null if not specified in the source */
    val receiverExpression: BoundExpression<*>?,
    /** non-null iff the function is invoked with the null-safe operator `?.`; implies [receiverExpression] != null */
    val nullSafeAccess: NullSafeAccess?,
    val functionNameToken: IdentifierToken,
    val valueArguments: List<BoundExpression<*>>,
    val candidateFilter: CandidateFilter?,
    val disambiguationBehavior: DisambiguationBehavior,
) : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression> {

    private val seanHelper = SeanHelper()

    /**
     * The result of the function dispatching. Is meaningful after [semanticAnalysisPhase2]; remains null after
     * phase 2 if the invoked function could not be resolved
     */
    val functionToInvoke: BoundFunction? get() = chosenOverload?.candidate
    private var chosenOverload: OverloadCandidateEvaluation? = null

    /** the type of the value returned by [functionToInvoke] */
    private val returnTypeOfInvokedFunction: BoundTypeReference? get() = chosenOverload?.returnType ?: chosenOverload?.candidate?.returnType

    override val type: BoundTypeReference? get() {
        val returnType = returnTypeOfInvokedFunction ?: return null
        return if (skipsInvocationOnNullReceiver) returnType.withCombinedNullability(TypeReference.Nullability.NULLABLE) else returnType
    }

    /**
     * Whether the invocation is skipped (and this expression evaluates to `null`) if the receiver evaluates to `null`.
     * True iff the invocation uses `?.` on a receiver of a nullable type.
     */
    private val skipsInvocationOnNullReceiver: Boolean
        get() = nullSafeAccess != null && receiverExceptReferringType?.type?.isNullable == true

    /**
     * The type of the receiver to consider for selecting the function to invoke. With `?.`, the invocation only
     * happens with a non-null receiver.
     */
    private val receiverTypeForDispatch: BoundTypeReference? get() {
        val receiverType = receiverExpression?.type ?: return null
        return if (nullSafeAccess != null) receiverType.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE) else receiverType
    }

    override val implications: List<BoundExpression.ResultImplication> get() {
        if (skipsInvocationOnNullReceiver) {
            // the result may also come from the receiver being null, the implications below don't hold
            return emptyList()
        }
        val fn = functionToInvoke ?: return emptyList()
        val arguments = listOfNotNull(receiverExpression) + valueArguments
        return when (fn.canonicalName) {
            // isNull(x) is true iff x evaluates to null
            EmergeConstants.CoreModule.IS_NULL_FN_NAME -> mapImplications(
                arguments.singleOrNull() ?: return emptyList(),
                ImplyingResult.NULL_VALUE to ImplyingResult.BOOL_TRUE,
                ImplyingResult.NON_NULL_VALUE to ImplyingResult.BOOL_FALSE,
            )
            EmergeConstants.CoreModule.BOOL_BITWISE_NOT_FN_NAME -> mapImplications(
                arguments.singleOrNull() ?: return emptyList(),
                ImplyingResult.BOOL_TRUE to ImplyingResult.BOOL_FALSE,
                ImplyingResult.BOOL_FALSE to ImplyingResult.BOOL_TRUE,
            )
            // `&` and `|` on Bool: both operands are evaluated (no short-circuiting): if `a & b` is true, both are true
            EmergeConstants.CoreModule.BOOL_BITWISE_AND_FN_NAME -> arguments.flatMap { mapImplications(it, ImplyingResult.BOOL_TRUE to ImplyingResult.BOOL_TRUE) }
            EmergeConstants.CoreModule.BOOL_BITWISE_OR_FN_NAME -> arguments.flatMap { mapImplications(it, ImplyingResult.BOOL_FALSE to ImplyingResult.BOOL_FALSE) }
            else -> emptyList()
        }
    }

    /**
     * @param mapping for each result of [argument]: the result of this invocation that it is implied by
     * @return the implications of [argument], for the results of this invocation
     */
    private fun mapImplications(argument: BoundExpression<*>, vararg mapping: Pair<ImplyingResult, ImplyingResult>): List<BoundExpression.ResultImplication> {
        return argument.implications.mapNotNull { implication ->
            val onResult = mapping.firstOrNull { it.first == implication.onResult }?.second ?: return@mapNotNull null
            BoundExpression.ResultImplication(onResult, implication.typeRefinements)
        }
    }

    var typeArguments: List<BoundTypeArgument>? = null
        private set

    /**
     * [receiverExpression], but `null` iff it is a direct referral to a [BoundBaseTypeDefinition]
     */
    private val receiverExceptReferringType: BoundExpression<*>?
        get() = receiverExpression?.takeUnless { it is BoundIdentifierExpression && it.referral is BoundIdentifierExpression.ReferringType }

    /** the context right after the invoked function returned; for [nullSafeAccess], only reached if the receiver is not null */
    private val contextAfterInvocation = MutableExecutionScopedCTContext.deriveFrom(context)

    /** for [nullSafeAccess]: where the receiver evaluated to null, so the arguments are not evaluated and the function is not invoked */
    private val contextWhenReceiverNull = nullSafeAccess?.let { MutableExecutionScopedCTContext.deriveFrom(receiverExpression!!.modifiedContext) }

    override val modifiedContext: ExecutionScopedCTContext = MutableExecutionScopedCTContext.deriveFrom(
        InvocationJoinExecutionScopedCTContext(
            contextBeforeInvocation,
            if (nullSafeAccess == null) contextAfterInvocation else SingleBranchJoinExecutionScopedCTContext(
                receiverExpression!!.modifiedContext,
                contextAfterInvocation,
                contextWhenReceiverNull!!,
            ),
        )
    )

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) =
        seanHelper.phase1(diagnosis) {
            receiverExpression?.semanticAnalysisPhase1(diagnosis)
            receiverExpression?.markEvaluationResultUsed()
            valueArguments.forEach { it.semanticAnalysisPhase1(diagnosis) }
            typeArguments = declaration.typeArguments?.map { context.resolveTypeArgument(it) }
            typeArguments?.forEach {
                if (it.astNode is AstWildcardTypeArgument) {
                    diagnosis.wildcardTypeArgumentOnInvocation(it)
                } else if (it.variance != TypeVariance.UNSPECIFIED) {
                    diagnosis.varianceOnInvocationTypeArgument(it)
                }
            }
        }

    private var evaluationResultUsed = false
    override fun markEvaluationResultUsed() {
        seanHelper.requirePhase1Done()
        seanHelper.requirePhase2NotDone()
        evaluationResultUsed = true
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            valueArguments.forEach { it.markEvaluationResultUsed() }

            receiverExpression?.semanticAnalysisPhase2(diagnosis)
            if (nullSafeAccess != null) {
                if (receiverExpression!!.type?.isNullable == false) {
                    diagnosis.superfluousSafeObjectTraversal(receiverExpression, nullSafeAccess.accessOperatorToken)
                }
                val receiverImplications = receiverExpression.implications
                VariableTypeRefinement.trackImplications(receiverImplications, ImplyingResult.NON_NULL_VALUE, nullSafeAccess.contextWhenReceiverNotNull)
                VariableTypeRefinement.trackImplications(receiverImplications, ImplyingResult.NULL_VALUE, contextWhenReceiverNull!!)
            }

            val availableOverloads: AvailableOverloads? = if (receiverExpression == null || (receiverExpression.type != null && receiverExpression.type !is ErroneousType)) {
                collectOverloadCandidates()
            } else {
                // receiver is present but type is not known -> cannot determine overload
                null
            }

            val singleOption = availableOverloads?.candidates?.singleOrNull()?.overloads?.singleOrNull()
            if (singleOption != null) {
                singleOption.parameters.parameters
                    .dropWhile { it === singleOption.parameters.declaredReceiver }
                    .zip(valueArguments)
                    .forEach { (parameter, argument) ->
                        parameter.typeAtDeclarationTime?.let { paramType ->
                            argument.setExpectedEvaluationResultType(paramType, diagnosis)
                        }
                    }
            } else if (availableOverloads != null) {
                inferTypesOfNumericLiteralArguments(availableOverloads, diagnosis)
            }

            typeArguments?.forEach { it.validate(TypeUseSite.Irrelevant(it.astNode.span, null), diagnosis) }
            valueArguments.forEach { it.semanticAnalysisPhase2(diagnosis) }

            if (availableOverloads == null) {
                return@phase2
            }

            chosenOverload = selectOverload(availableOverloads, diagnosis) ?: return@phase2

            (chosenOverload!!.candidate as? BoundClassConstructor)
                ?.takeIf { it.classDef.isUnique && !declaration.span.generated }
                ?.let { diagnosis.add(UniqueClassConstructorInvocationDiagnostic(it.classDef.simpleName, declaration.span)) }

            contextAfterInvocation.trackSideEffect(CallFrameExit.Effect.InvokesFunction(chosenOverload!!.candidate.callFrameExitEffectOnInvocation))

            if (chosenOverload!!.returnType == null) {
                handleCyclicInvocation(
                    context = this,
                    action = { chosenOverload!!.candidate.semanticAnalysisPhase2(diagnosis) },
                    onCycle = {
                        diagnosis.typeDeductionError(
                            "Cannot infer return type of the call to function ${functionNameToken.value} because the inference is cyclic here. Specify the return type explicitly.",
                            declaration.span,
                        )
                    }
                )
            }

            val candidate = chosenOverload!!.candidate
            candidate.parameters.parameters.zip(listOfNotNull(receiverExceptReferringType) + valueArguments)
                .forEach { (parameter, argument) ->
                    argument.setEvaluationResultUsage(CreateReferenceValueUsage(
                        parameter.typeAtDeclarationTime
                            ?.withTypeVariables(candidate.allTypeParameters)
                            ?.instantiateFreeVariables(chosenOverload!!.unification),
                        parameter.declaration.span,
                        parameter.ownershipAtDeclarationTime,
                    ))
                }
        }
    }

    /**
     * A numeric literal can only be an argument to a parameter of a numeric type. If, among all the overloads,
     * those parameters agree on the type, the literal takes that type; just as it does when there is only one overload.
     */
    private fun inferTypesOfNumericLiteralArguments(availableOverloads: AvailableOverloads, diagnosis: Diagnosis) {
        val overloads = availableOverloads.candidates.flatMap { it.overloads }
        valueArguments.forEachIndexed { argumentIndex, argument ->
            if (argument !is BoundNumericLiteral) {
                return@forEachIndexed
            }

            val numericParameterTypes = overloads
                .mapNotNull { overload ->
                    overload.parameters.parameters
                        .dropWhile { it === overload.parameters.declaredReceiver }
                        .takeIf { it.size == valueArguments.size }
                        ?.get(argumentIndex)
                        ?.typeAtDeclarationTime
                        ?.let { it as? RootResolvedTypeReference }
                        ?.takeIf { it.baseType.isCoreNumericType }
                }
                .distinctBy { it.baseType }

            numericParameterTypes.singleOrNull()?.let { argument.setExpectedEvaluationResultType(it, diagnosis) }
        }
    }

    private fun collectOverloadCandidates(): AvailableOverloads {
        assert((receiverExpression == null) xor (receiverExpression?.type != null))

        val candidateConstructors: Collection<BoundOverloadSet<*>>? = if (receiverExpression != null) null else {
            context.resolveBaseType(functionNameToken.value)
                .distinct()
                .mapNotNull { it.constructor }
                .map { BoundOverloadSet.fromSingle(it) }
                .toList()
                .takeUnless { it.isEmpty() }
        }
        val candidateTopLevelFunctions = context.getToplevelFunctionOverloadSetsBySimpleName(functionNameToken.value).distinct()
        val candidateMemberFunctions = receiverTypeForDispatch?.findMemberFunction(functionNameToken.value) ?: emptySet()

        val allCandidates = (candidateConstructors ?: emptySet()) + candidateTopLevelFunctions + candidateMemberFunctions

        return AvailableOverloads(
            allCandidates,
            candidateConstructors != null,
            candidateTopLevelFunctions.isNotEmpty(),
        )
    }

    /**
     * Selects one of the given overloads, including ones that are not a legal match if there are no legal alternatives.
     * Also performs the following checks and reports accordingly:
     * * absolutely no candidate available to evaluate
     * * of the evaluated constructors or functions, none match
     * * if there is only one overload to pick from, forwards any diagnostics from evaluating that candidate
     */
    private fun selectOverload(overloadCandidates: AvailableOverloads, diagnosis: Diagnosis): OverloadCandidateEvaluation? {
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

        val (allCandidates, constructorsConsidered, anyTopLevelFunctions) = overloadCandidates

        if (allCandidates.isEmpty()) {
            diagnosis.noMatchingFunctionOverload(context, functionNameToken, receiverTypeForDispatch, valueArguments, false, emptyList())
            return null
        }

        val evaluations = allCandidates.evaluateInvocationCandidates(
            // for static member fns, receiverExpression helps discover them. But for the actual invocation,
            // the receiver stops to matter
            receiverExceptReferringType,
        ).toSet()

        if (evaluations.isEmpty()) {
            // TODO: pass on the mismatch reason for all candidates?
            if (constructorsConsidered) {
                diagnosis.unresolvableConstructor(
                    functionNameToken,
                    valueArguments,
                    anyTopLevelFunctions,
                )
            } else {
                diagnosis.noMatchingFunctionOverload(
                    context,
                    functionNameToken,
                    receiverTypeForDispatch,
                    valueArguments,
                    anyTopLevelFunctions,
                    emptyList(),
                )
            }

            return null
        }

        val legalMatches = evaluations.filter { it.isLegalCandidate }
        when (legalMatches.size) {
            0 -> {
                val (applicableInvalidCandidates, inapplicableCandidates) = evaluations.partition { it.inapplicableReason == null }
                if (applicableInvalidCandidates.size == 1) {
                    val singleEval = applicableInvalidCandidates.single()
                    // if there is only a single candidate, the errors found in validating are 100% applicable to be shown to the user
                    singleEval.unification.diagnostics
                        .also { diags ->
                            check(diags.any { it.severity >= Diagnostic.Severity.ERROR }) {
                                "Cannot choose overload to invoke, but evaluation of single overload candidate didn't yield any error -- what?"
                            }
                        }
                        .forEach(diagnosis::add)

                    return singleEval
                }

                val disjointParameterIndices = applicableInvalidCandidates.indicesOfDisjointlyTypedParameters().toSet()
                val reducedEvaluations =
                    applicableInvalidCandidates.filter { it.indicesOfErroneousParameters.none { it in disjointParameterIndices } }
                if (reducedEvaluations.size == 1) {
                    val singleEval = reducedEvaluations.single()
                    singleEval.unification.diagnostics.forEach(diagnosis::add)
                    return singleEval
                } else {
                    diagnosis.noMatchingFunctionOverload(
                        context,
                        functionNameToken,
                        receiverTypeForDispatch,
                        valueArguments,
                        functionDeclaredAtAll = true,
                        inapplicableCandidates.map { it.inapplicableReason!! }
                    )
                    return applicableInvalidCandidates.firstOrNull()
                }
            }
            1 -> return legalMatches.single()
            else -> {
                if (legalMatches.all { it.candidate is InheritedBoundMemberFunction }) {
                    legalMatches
                        .map { it.candidate as InheritedBoundMemberFunction }
                        .let(InheritedBoundMemberFunction::closestCommonOverriddenFunction)
                        ?.let { commonOverriddenFn ->
                            sequenceOf(commonOverriddenFn).evaluateInvocationCandidates(receiverExceptReferringType).firstOrNull()
                        }
                        ?.let { return it }
                }
                diagnosis.ambiguousInvocation(
                    this,
                    evaluations
                        .filter { it.inapplicableReason == null }
                        .map { it.candidate }
                )
                return legalMatches.firstOrNull()
            }
        }
    }

    private fun Iterable<BoundOverloadSet<*>>.evaluateInvocationCandidates(receiver: BoundExpression<*>?): Sequence<OverloadCandidateEvaluation> {
        return this.asSequence()
            .flatMap { it.overloads }
            .evaluateInvocationCandidates(receiver)
    }

    private fun Sequence<BoundFunction>.evaluateInvocationCandidates(
        receiver: BoundExpression<*>?,
    ): Sequence<OverloadCandidateEvaluation> {
        check((receiver != null) xor (receiver?.type == null))
        val receiverType = if (receiver == null) null else receiverTypeForDispatch
        val argumentsIncludingReceiver = listOfNotNull(receiver) + valueArguments
        val argumentTypesIncludingReceiver = listOfNotNull(receiverType) + valueArguments.map { it.type!! }

        return this
            // filter by (declared receiver)
            .filter { candidateFn -> (receiverType != null) == candidateFn.declaresReceiver }
            // filter by incompatible number of parameters
            .filter { it.parameters.parameters.size == argumentsIncludingReceiver.size }
            .mapNotNull { candidateFn ->
                if (candidateFn.parameterTypes.any { it == null }) {
                    // types not fully resolved, don't consider
                    return@mapNotNull null
                }

                val returnTypeArgsLocation = typeArguments
                    ?.mapNotNull { it.astNode.span }
                    ?.reduce(Span::rangeTo)
                    ?: declaration.span
                val returnTypeWithVariables = candidateFn.returnType?.withTypeVariables(candidateFn.allTypeParameters)

                @Suppress("UNCHECKED_CAST") // the check is right above
                val rightSideTypes = (candidateFn.parameterTypes as List<BoundTypeReference>)
                    .map { it.withTypeVariables(candidateFn.allTypeParameters) }
                check(rightSideTypes.size == argumentsIncludingReceiver.size)

                val indicesOfErroneousParameters = ArrayList<Int>(argumentsIncludingReceiver.size)
                val unificationBeforeParameters = TypeUnification.fromExplicit(
                    candidateFn.allTypeParameters,
                    candidateFn.declaredTypeParameters,
                    typeArguments,
                    returnTypeArgsLocation,
                    allowMissingTypeArguments = true,
                    capturableParameters = if (candidateFn.declaresReceiver) {
                        candidateFn.allTypeParameters.toSet() - candidateFn.declaredTypeParameters.toSet()
                    } else {
                        emptySet()
                    },
                )
                val unificationAfterParameters = argumentsIncludingReceiver
                    .zip(argumentTypesIncludingReceiver)
                    .zip(rightSideTypes)
                    .foldIndexed(unificationBeforeParameters) { parameterIndex, carryUnification, (argumentAndType, parameterType) ->
                        val (argument, argumentType) = argumentAndType
                        val unificationAfterParameter = parameterType.unify(argumentType, argument.declaration.span, carryUnification)
                        if (unificationAfterParameter.getErrorsNotIn(carryUnification).any()) {
                            indicesOfErroneousParameters.add(parameterIndex)
                        }
                        unificationAfterParameter
                    }
                val unificationAfterExpectedType = expectedEvaluationResultType
                    ?.let { expectedType ->
                        returnTypeWithVariables?.let { unificationAfterParameters.plusExpectedTypeForOwnValues(it, expectedType, declaration.span) }
                    }
                    ?: unificationAfterParameters
                val unification = unificationAfterExpectedType.plusFinalValueChecks(declaration.span)

                val inapplicableReason = when (val inspectResult = candidateFilter?.inspect(candidateFn)) {
                    null, Result.Applicable -> null
                    is Result.Inapplicable -> inspectResult.reason
                }

                val allDisambiguatingArgumentsAreErrorFree = if (disambiguationBehavior == DisambiguationBehavior.AllParametersDisambiguate) {
                    indicesOfErroneousParameters.isEmpty()
                } else {
                    indicesOfErroneousParameters.none { erroneousParamIndex ->
                        val param = candidateFn.parameters.parameters[erroneousParamIndex]
                        disambiguationBehavior.shouldDisambiguateOnParameter(candidateFn, param, erroneousParamIndex.toUInt())
                    }
                }

                OverloadCandidateEvaluation(
                    candidateFn,
                    unification,
                    returnTypeWithVariables?.instantiateFreeVariables(unification),
                    indicesOfErroneousParameters,
                    inapplicableReason,
                    isLegalCandidate = unificationBeforeParameters.diagnostics.none { it.severity >= Diagnostic.Severity.ERROR }
                        && inapplicableReason == null
                        && allDisambiguatingArgumentsAreErrorFree
                        && unification.getErrorsNotIn(unificationAfterExpectedType).none()
                )
            }
    }

    private var nothrowBoundary: NothrowViolationDiagnostic.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        this.nothrowBoundary = boundary
        receiverExpression?.setNothrow(boundary)
        valueArguments.forEach { it.setNothrow(boundary) }
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // nothing to do; a function return type can always be captured and purity is checked fully
        // inside the function implementation.
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            receiverExpression?.semanticAnalysisPhase3(diagnosis)

            valueArguments.forEach { it.semanticAnalysisPhase3(diagnosis) }
            functionToInvoke?.let { targetFn ->
                targetFn.validateAccessFrom(functionNameToken.span, diagnosis)
                nothrowBoundary?.let { nothrowBoundary ->
                    if (targetFn.callFrameExitEffectOnInvocation.throws != CallFrameExit.Occurrence.NEVER) {
                        diagnosis.nothrowViolatingInvocation(this, nothrowBoundary)
                    }
                }
            }
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase2Done()

        receiverExpression?.visitReadsBeyond(boundary, visitor)
        valueArguments.forEach { it.visitReadsBeyond(boundary, visitor) }
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase2Done()

        receiverExpression?.visitWritesBeyond(boundary, visitor)
        valueArguments.forEach { it.visitWritesBeyond(boundary, visitor) }
    }

    private var expectedEvaluationResultType: BoundTypeReference? = null

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        seanHelper.requirePhase2NotDone()
        expectedEvaluationResultType = type
    }

    override val isEvaluationResultReferenceCounted = true
    override val isEvaluationResultAnchored = false
    override val isCompileTimeConstant: Boolean
        get() {
            val localDispatchedFunction = functionToInvoke ?: return false
            if (localDispatchedFunction.attributes.externalAttribute != null) {
                // what an external function does is not known to the compiler
                return false
            }
            val receiverIsConstant = receiverExpression?.isCompileTimeConstant ?: true
            return receiverIsConstant && valueArguments.all { it.isCompileTimeConstant }
        }

    private fun buildBackendIrInvocation(
        arguments: List<IrTemporaryValueReference>,
        landingpad: IrInvocationExpression.Landingpad?,
    ): IrInvocationExpression {
        val isCallOnAbstractType = receiverTypeForDispatch?.baseTypeOfLowerBound?.kind?.allowsSubtypes == true
        val fn = functionToInvoke!!
        val returnType = returnTypeOfInvokedFunction!!.toBackendIr()
        val irResolvedTypeArgs = chosenOverload!!.unification.bindings
            .associate { (parameter, binding) -> parameter.name to binding.toBackendIr() }

        // TODO: doesn't this lead to static dispatch when calling methods on generic types??
        if (fn is BoundMemberFunction && fn.isVirtual!! && isCallOnAbstractType) {
            check(receiverExceptReferringType != null)
            return IrDynamicDispatchFunctionInvocationImpl(
                arguments.first(),
                fn.toBackendIr(),
                arguments,
                irResolvedTypeArgs,
                returnType,
                landingpad,
            )
        }

        return IrStaticDispatchFunctionInvocationImpl(
            functionToInvoke!!.toBackendIr(),
            arguments,
            irResolvedTypeArgs,
            returnType,
            landingpad,
        )
    }

    override fun toBackendIrExpression(): IrExpression = toBackendIrExpression { emptyList() }
    fun toBackendIrExpression(buildAdditionalResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable>): IrImplicitEvaluationExpression {
        if (!skipsInvocationOnNullReceiver) {
            return buildInvocationIr(
                listOfNotNull(receiverExceptReferringType).map { it.prepareAsArgument() },
                buildAdditionalResultCleanup,
            )
        }

        // receiver?.fn(args) evaluates to: if isNull(receiver) null else fn(receiver, args)
        val nullSafeIr = buildNullSafeInvocationIr(buildAdditionalResultCleanup)
        val irType = type!!.toBackendIr()
        val nullTemporary = IrCreateTemporaryValueImpl(IrNullLiteralExpressionImpl(irType))
        val resultTemporary = IrCreateTemporaryValueImpl(IrIfExpressionImpl(
            nullSafeIr.receiverIsNull,
            IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(listOf(nullTemporary)),
                IrTemporaryValueReferenceImpl(nullTemporary),
            ),
            nullSafeIr.invocation,
            irType,
        ))

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(nullSafeIr.evaluateReceiver + resultTemporary),
            IrTemporaryValueReferenceImpl(resultTemporary),
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        val dropResult: (IrTemporaryValueReference) -> List<IrExecutable> = { listOf(IrDropStrongReferenceStatementImpl(it)) }
        if (!skipsInvocationOnNullReceiver) {
            return toBackendIrExpression(dropResult).code
        }

        // receiver?.fn(args) as a statement is: if not isNull(receiver) { fn(receiver, args) }
        val nullSafeIr = buildNullSafeInvocationIr(dropResult)
        return IrCodeChunkImpl(nullSafeIr.evaluateReceiver + IrConditionalBranchImpl(
            nullSafeIr.receiverIsNull,
            IrCodeChunkImpl(emptyList()),
            nullSafeIr.invocation.code,
        ))
    }

    /**
     * @param preparedReceiver the receiver, if any. Must be prepared by the caller because the receiver might be
     * evaluated before the code returned by this function, see [buildNullSafeInvocationIr].
     */
    private fun buildInvocationIr(
        preparedReceiver: List<PreparedInvocationArgument>,
        buildAdditionalResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable>,
    ): IrImplicitEvaluationExpression {
        return buildGenericInvocationLikeIrWithPreparedArguments(
            context,
            declaration.span,
            preparedReceiver + valueArguments.map { it.prepareAsArgument() },
            ::buildBackendIrInvocation,
            buildResultCleanup = { resultTemporary ->
                val unreachable = when {
                    functionToInvoke!!.callFrameExitEffectOnInvocation.throws == CallFrameExit.Occurrence.GUARANTEED -> {
                        listOf(IrUnreachableStatementImpl("function $functionToInvoke reports that it is guaranteed to throw", true))
                    }
                    functionToInvoke!!.returnType!!.isNonNullableNothing -> {
                        listOf(IrUnreachableStatementImpl("function $functionToInvoke returns emerge.core.Nothing!", true))
                    }
                    else -> emptyList()
                }

                unreachable + buildAdditionalResultCleanup(resultTemporary)
            },
            assumeNothrow = functionToInvoke!!.attributes.isDeclaredNothrow,
        )
    }

    private fun buildNullSafeInvocationIr(buildAdditionalResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable>): NullSafeInvocationIr {
        check(skipsInvocationOnNullReceiver)
        val receiver = receiverExceptReferringType!!.prepareAsArgument()
        val receiverIsNull = IrCreateTemporaryValueImpl(IrIsNullExpressionImpl(receiver.reference, context.swCtx))

        // the receiver is evaluated before the null-check; only its cleanup is part of the invocation
        val receiverInInvocation = PreparedInvocationArgument(
            prepareCode = emptyList(),
            // for value types, this unboxes the receiver
            reference = IrTemporaryValueReferenceImpl(receiver.reference.declaration, receiverTypeForDispatch!!.toBackendIr()),
            cleanupCode = receiver.cleanupCode,
        )

        return NullSafeInvocationIr(
            receiver.prepareCode + receiverIsNull,
            IrTemporaryValueReferenceImpl(receiverIsNull),
            buildInvocationIr(listOf(receiverInInvocation), buildAdditionalResultCleanup),
        )
    }

    private class NullSafeInvocationIr(
        /** evaluates the receiver and checks whether it is null */
        val evaluateReceiver: List<IrExecutable>,
        /** whether the receiver is null, is defined after [evaluateReceiver] */
        val receiverIsNull: IrTemporaryValueReference,
        /** the invocation itself, given that [receiverIsNull] is false */
        val invocation: IrImplicitEvaluationExpression,
    )

    class NullSafeAccess(
        /** the `?.` operator */
        val accessOperatorToken: OperatorToken,
        /**
         * Derived conditionally from the [BoundExpression.modifiedContext] of the receiver: the arguments are evaluated
         * and the function is invoked only if the receiver is not null.
         */
        val contextWhenReceiverNotNull: MutableExecutionScopedCTContext,
    )

    /**
     * Used to filter the available functions before selecting one to invoke. The [Result.Inapplicable.reason]s
     * will be reported back to the user to provide a better understanding of the problem.
     */
    fun interface CandidateFilter {
        /**
         * Inspects the given candidate function and returns info on how to treat this candidate.
         */
        fun inspect(candidate: BoundFunction): Result

        sealed interface Result {
            object Applicable : Result
            class Inapplicable(val reason: InvocationCandidateNotApplicableDiagnostic) : Result
        }
    }

    fun interface DisambiguationBehavior {
        /**
         * @return whether the parameter [parameter] of candidate [candidate] (which is at index [parameterIndex], 0 being a possible receiver),
         * should contribute to disambiguation.
         */
        fun shouldDisambiguateOnParameter(candidate: BoundFunction, parameter: BoundParameter, parameterIndex: UInt): Boolean

        object AllParametersDisambiguate : DisambiguationBehavior {
            override fun shouldDisambiguateOnParameter(
                candidate: BoundFunction,
                parameter: BoundParameter,
                parameterIndex: UInt
            ): Boolean {
                return true
            }
        }
    }
}

private data class AvailableOverloads(
    val candidates: Collection<BoundOverloadSet<*>>,
    val constructorsConsidered: Boolean,
    val anyTopLevelFunctions: Boolean,
)

private data class OverloadCandidateEvaluation(
    val candidate: BoundFunction,
    val unification: TypeUnification,
    val returnType: BoundTypeReference?,
    val indicesOfErroneousParameters: Collection<Int>,
    val inapplicableReason: InvocationCandidateNotApplicableDiagnostic?,
    val isLegalCandidate: Boolean,
)

private fun Collection<OverloadCandidateEvaluation>.indicesOfDisjointlyTypedParameters(): Sequence<Int> {
    if (isEmpty()) {
        return emptySequence()
    }

    return (0 until first().candidate.parameters.parameters.size).asSequence()
        .filter { parameterIndex ->
            val parameterTypesAtIndex = this.map { it.candidate.parameters.parameters[parameterIndex] }
            parameterTypesAtIndex.nonDisjointPairs().none()
        }
}

internal class IrStaticDispatchFunctionInvocationImpl(
    override val function: IrFunction,
    override val arguments: List<IrTemporaryValueReference>,
    override val typeArgumentsAtCallSite: Map<String, IrType>,
    override val evaluatesTo: IrType,
    override val landingpad: IrInvocationExpression.Landingpad?,
) : IrStaticDispatchFunctionInvocationExpression

internal class IrDynamicDispatchFunctionInvocationImpl(
    override val dispatchOn: IrTemporaryValueReference,
    override val function: IrMemberFunction,
    override val arguments: List<IrTemporaryValueReference>,
    override val typeArgumentsAtCallSite: Map<String, IrType>,
    override val evaluatesTo: IrType,
    override val landingpad: IrInvocationExpression.Landingpad?,
) : IrDynamicDispatchFunctionInvocationExpression

/**
 * An argument to an invocation, evaluated into a temporary.
 */
internal class PreparedInvocationArgument(
    /** evaluates the argument; [reference] is defined after this code */
    val prepareCode: List<IrExecutable>,
    /** the argument value */
    val reference: IrTemporaryValueReference,
    /** to be executed after the invocation has returned */
    val cleanupCode: List<IrExecutable>,
)

internal fun BoundExpression<*>.prepareAsArgument(): PreparedInvocationArgument {
    val temporary = IrCreateTemporaryValueImpl(toBackendIrExpression())
    val prepareCode = ArrayList<IrExecutable>(2)
    val cleanupCode = ArrayList<IrExecutable>(1)
    prepareCode.add(temporary)
    if (!isEvaluationResultAnchored) {
        if (!isEvaluationResultReferenceCounted) {
            // refcount to keep alive during the evaluation of subsequent temporaries
            prepareCode.add(IrCreateStrongReferenceStatementImpl(temporary))
        }
        if (isEvaluationResultReferenceCounted) {
            // use of the temporary is over after the call, drop the reference
            cleanupCode.add(IrDropStrongReferenceStatementImpl(temporary))
        }
    } // else: if anchored we don't need to refcount the temporary

    return PreparedInvocationArgument(prepareCode, IrTemporaryValueReferenceImpl(temporary), cleanupCode)
}

/**
 * common base for [buildGenericInvocationLikeIr] and [buildNothrowInvocationLikeIr]
 */
private fun buildInvocationLikeIrInternal(
    arguments: List<PreparedInvocationArgument>,
    buildActualCall: (arguments: List<IrTemporaryValueReference>, argumentsCleanupCode: List<IrExecutable>) -> IrExpression,
    buildResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable>,
): IrImplicitEvaluationExpression {
    val prepareArgumentsCode = arguments.flatMap { it.prepareCode }
    val cleanUpArgumentsCode = arguments.flatMap { it.cleanupCode }

    val returnValueTemporary = IrCreateTemporaryValueImpl(
        buildActualCall(
            arguments.map { it.reference },
            cleanUpArgumentsCode,
        )
    )
    val returnValueTemporaryRef = IrTemporaryValueReferenceImpl(returnValueTemporary)
    val cleanupCode = buildResultCleanup(returnValueTemporaryRef)
    return IrImplicitEvaluationExpressionImpl(
        IrCodeChunkImpl(prepareArgumentsCode + returnValueTemporary + cleanUpArgumentsCode + cleanupCode),
        returnValueTemporaryRef,
    )
}

/**
 * like [buildGenericInvocationLikeIr], but assumes the caller knows the invocation is nothrow
 */
internal fun buildNothrowInvocationLikeIr(
    boundArgumentExprs: List<BoundExpression<*>>,
    buildActualCall: (arguments: List<IrTemporaryValueReference>) -> IrExpression,
    buildResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable> = { emptyList() },
): IrImplicitEvaluationExpression {
    return buildInvocationLikeIrInternal(
        boundArgumentExprs.map { it.prepareAsArgument() },
        { args, _ -> buildActualCall(args) },
        buildResultCleanup,
    )
}

/**
 * Contains logic for invocation-like IR. Used for actual invocations, but also e.g. for [BoundArrayLiteralExpression].
 * Doesn't assume any value for [BoundExpression.isEvaluationResultReferenceCounted]; refcounting logic can be cleanly
 * customized with [buildResultCleanup].
 *
 * @param assumeNothrow if true, [buildActualCall] will not receive a landingpad
 */
internal fun buildGenericInvocationLikeIr(
    context: ExecutionScopedCTContext,
    invocationLocation: Span,
    boundArgumentExprs: List<BoundExpression<*>>,
    buildActualCall: (arguments: List<IrTemporaryValueReference>, landingpad: IrInvocationExpression.Landingpad?) -> IrExpression,
    buildResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable> = { emptyList() },
    assumeNothrow: Boolean,
): IrImplicitEvaluationExpression {
    return buildGenericInvocationLikeIrWithPreparedArguments(
        context,
        invocationLocation,
        boundArgumentExprs.map { it.prepareAsArgument() },
        buildActualCall,
        buildResultCleanup,
        assumeNothrow,
    )
}

/**
 * Like [buildGenericInvocationLikeIr], but the arguments have been [prepareAsArgument]ed by the caller.
 */
private fun buildGenericInvocationLikeIrWithPreparedArguments(
    context: ExecutionScopedCTContext,
    invocationLocation: Span,
    arguments: List<PreparedInvocationArgument>,
    buildActualCall: (arguments: List<IrTemporaryValueReference>, landingpad: IrInvocationExpression.Landingpad?) -> IrExpression,
    buildResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable>,
    assumeNothrow: Boolean,
): IrImplicitEvaluationExpression {
    return buildInvocationLikeIrInternal(
        arguments,
        { args, argsCleanupCode ->
            val landingpad = if (assumeNothrow) null else {
                val cleanupCode = argsCleanupCode + context.getExceptionHandlingLocalDeferredCode().mapToBackendIrWithDebugLocations()
                val landingpadContext = MutableExecutionScopedCTContext.deriveFrom(context)
                val throwableVar = VariableDeclaration(
                    invocationLocation,
                    AstAnnotationSet.EMPTY,
                    null,
                    null,
                    null,
                    IdentifierToken(
                        landingpadContext.findInternalVariableName("t"),
                        invocationLocation
                    ),
                    NamedTypeReference(IdentifierToken(context.swCtx.throwable.simpleName, invocationLocation)),
                    null,
                ).bindTo(landingpadContext)
                throwableVar.semanticAnalysisPhase1(Diagnosis.failOnError())
                throwableVar.semanticAnalysisPhase2(Diagnosis.failOnError())
                throwableVar.semanticAnalysisPhase3(Diagnosis.failOnError())
                landingpadContext.addVariable(throwableVar)

                val exceptionTemporary = IrCreateTemporaryValueImpl(
                    IrVariableAccessExpressionImpl(throwableVar.backendIrDeclaration)
                )
                val rethrowStmt = IrCodeChunkImpl(
                    // also when an Error passes by the catch, the scopes around the try have to be cleaned up
                    context.getDeferredCodeForUncatchableThrow().mapToBackendIrWithDebugLocations()
                    +
                    listOf(IrThrowStatementImpl(IrTemporaryValueReferenceImpl(exceptionTemporary), ignoreLocalCatchBlock = true))
                )
                val catchOrRethrow: List<IrExecutable> = if (context.isInTryContext) {
                    val isError = IrCreateTemporaryValueImpl(buildInstanceOf(
                        landingpadContext.swCtx,
                        IrTemporaryValueReferenceImpl(exceptionTemporary),
                        landingpadContext.swCtx.error.getBoundReferenceAssertNoTypeParameters(),
                        null,
                    ))

                    val catchOrThrowBranch = IrConditionalBranchImpl(
                        condition = IrTemporaryValueReferenceImpl(isError),
                        thenBranch = rethrowStmt,
                        elseBranch = IrCatchExceptionStatementImpl(IrTemporaryValueReferenceImpl(exceptionTemporary)),
                    )

                    listOf(isError, catchOrThrowBranch)
                } else {
                    listOf(rethrowStmt)
                }

                IrInvocationExpression.Landingpad(
                    throwableVar.backendIrDeclaration,
                    IrCodeChunkImpl(cleanupCode + exceptionTemporary + catchOrRethrow),
                )
            }

            buildActualCall(args, landingpad)
        },
        buildResultCleanup,
    )
}

private class IrCatchExceptionStatementImpl(
    override val exceptionReference: IrTemporaryValueReference
) : IrCatchExceptionStatement