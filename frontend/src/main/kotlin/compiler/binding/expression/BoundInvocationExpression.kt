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
import compiler.ast.VariableDeclaration
import compiler.ast.expression.InvocationExpression
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.SideEffectPrediction.Companion.reduceSequentialExecution
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.impurity.ImpureInvocation
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.*
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.InvocationCandidateNotApplicableDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.ambiguousInvocation
import compiler.diagnostic.noMatchingFunctionOverload
import compiler.diagnostic.nothrowViolatingInvocation
import compiler.diagnostic.typeDeductionError
import compiler.diagnostic.unresolvableConstructor
import compiler.diagnostic.varianceOnInvocationTypeArgument
import compiler.handleCyclicInvocation
import compiler.lexer.IdentifierToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrCatchExceptionStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDynamicDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundInvocationExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: InvocationExpression,
    /** The receiver expression; is null if not specified in the source */
    val receiverExpression: BoundExpression<*>?,
    val functionNameToken: IdentifierToken,
    val valueArguments: List<BoundExpression<*>>,
) : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression> {

    private val seanHelper = SeanHelper()

    /**
     * Can only be set **before** [semanticAnalysisPhase2], and can only ever be set once.
     * Repeated sets to the same object (by identity) are tolerated.
     */
    var candidateFilter: CandidateFilter? = null
        set(value) {
            seanHelper.requirePhase2NotDone()
            if (field != null && field !== value) {
                throw InternalCompilerError("The ${::candidateFilter.name} can only be set once")
            }
            field = value
        }

    /**
     * The result of the function dispatching. Is meaningful after [semanticAnalysisPhase2]; remains null after
     * phase 2 if the invoked function could not be resolved
     */
    val functionToInvoke: BoundFunction? get() = chosenOverload?.candidate
    private var chosenOverload: OverloadCandidateEvaluation? = null

    override val type: BoundTypeReference? get() = chosenOverload?.returnType ?: chosenOverload?.candidate?.returnType

    var typeArguments: List<BoundTypeArgument>? = null
        private set

    /**
     * [receiverExpression], but `null` iff it is a direct referral to a [BoundBaseTypeDefinition]
     */
    private val receiverExceptReferringType: BoundExpression<*>?
        get() = receiverExpression?.takeUnless { it is BoundIdentifierExpression && it.referral is BoundIdentifierExpression.ReferringType }

    override val throwBehavior: SideEffectPrediction? get() {
        val behaviors = valueArguments.map { it.throwBehavior } + listOf(functionToInvoke?.throwBehavior)
        return behaviors.reduceSequentialExecution()
    }

    override val returnBehavior: SideEffectPrediction? get() {
        val behaviors = valueArguments.map { it.returnBehavior } + listOf(SideEffectPrediction.NEVER)
        return behaviors.reduceSequentialExecution()
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) =
        seanHelper.phase1(diagnosis) {
            receiverExpression?.semanticAnalysisPhase1(diagnosis)
            receiverExpression?.markEvaluationResultUsed()
            valueArguments.forEach { it.semanticAnalysisPhase1(diagnosis) }
            typeArguments = declaration.typeArguments?.map(context::resolveType)
            typeArguments?.forEach {
                if (it.variance != TypeVariance.UNSPECIFIED) {
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

            val availableOverloads: AvailableOverloads? = if (receiverExpression == null || (receiverExpression.type != null && receiverExpression.type !is UnresolvedType)) {
                collectOverloadCandidates()
            } else {
                // receiver is present but type is not known -> cannot determine overload
                null
            }

            availableOverloads?.candidates?.singleOrNull()?.overloads?.singleOrNull()?.let { singleOption ->
                singleOption.parameters.parameters
                    .dropWhile { it === singleOption.parameters.declaredReceiver }
                    .zip(valueArguments)
                    .forEach { (parameter, argument) ->
                        parameter.typeAtDeclarationTime?.let { paramType ->
                            argument.setExpectedEvaluationResultType(paramType, diagnosis)
                        }
                    }
            }

            typeArguments?.forEach { it.validate(TypeUseSite.Irrelevant(it.astNode.span, null), diagnosis) }
            valueArguments.forEach { it.semanticAnalysisPhase2(diagnosis) }

            if (availableOverloads == null) {
                return@phase2
            }

            chosenOverload = selectOverload(availableOverloads, diagnosis) ?: return@phase2

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

            chosenOverload!!.candidate.parameters.parameters.zip(listOfNotNull(receiverExceptReferringType) + valueArguments)
                .forEach { (parameter, argument) ->
                    argument.setEvaluationResultUsage(CreateReferenceValueUsage(
                        parameter.typeAtDeclarationTime,
                        parameter.declaration.span,
                        parameter.ownershipAtDeclarationTime,
                    ))
                }
        }
    }

    private fun collectOverloadCandidates(): AvailableOverloads {
        assert((receiverExpression == null) xor (receiverExpression?.type != null))

        val candidateConstructors = if (receiverExpression != null) null else {
            context.resolveBaseType(functionNameToken.value)
                ?.constructor
                ?.let { BoundOverloadSet.fromSingle(it) }
                ?.let(::setOf)
        }
        val candidateTopLevelFunctions = context.getToplevelFunctionOverloadSetsBySimpleName(functionNameToken.value)
        val candidateMemberFunctions = receiverExpression?.type?.findMemberFunction(functionNameToken.value) ?: emptySet()

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
            diagnosis.noMatchingFunctionOverload(functionNameToken, receiverExpression?.type, valueArguments, false, emptyList())
            return null
        }

        val evaluations = allCandidates.filterAndSortByMatchForInvocationTypes(
            // for static member fns, receiverExpression helps discover them. But for the actual invocation,
            // the receiver stops to matter
            receiverExceptReferringType,
        )

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
                    functionNameToken,
                    receiverExpression?.type,
                    valueArguments,
                    anyTopLevelFunctions,
                    emptyList(),
                )
            }

            return null
        }

        val legalMatches = evaluations.filter { !it.hasErrors }
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
                        functionNameToken,
                        receiverExpression?.type,
                        valueArguments,
                        functionDeclaredAtAll = true,
                        inapplicableCandidates.map { it.inapplicableReason!! }
                    )
                    return applicableInvalidCandidates.firstOrNull()
                }
            }
            1 -> return legalMatches.single()
            else -> {
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
    private fun Iterable<BoundOverloadSet<*>>.filterAndSortByMatchForInvocationTypes(
        receiver: BoundExpression<*>?,
    ): List<OverloadCandidateEvaluation> {
        check((receiver != null) xor (receiver?.type == null))
        val receiverType = receiver?.type
        val argumentsIncludingReceiver = listOfNotNull(receiver) + valueArguments
        return this
            .asSequence()
            .filter { it.parameterCount == argumentsIncludingReceiver.size }
            .flatMap { it.overloads }
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
                var unification = TypeUnification.fromExplicit(candidateFn.declaredTypeParameters, typeArguments, returnTypeArgsLocation, allowMissingTypeArguments = true)
                if (returnTypeWithVariables != null) {
                    if (expectedEvaluationResultType != null) {
                        unification = unification.doWithIgnoringReportings { obliviousUnification ->
                            expectedEvaluationResultType!!.unify(returnTypeWithVariables, Span.UNKNOWN, obliviousUnification)
                        }
                    }
                }

                @Suppress("UNCHECKED_CAST") // the check is right above
                val rightSideTypes = (candidateFn.parameterTypes as List<BoundTypeReference>)
                    .map { it.withTypeVariables(candidateFn.allTypeParameters) }
                check(rightSideTypes.size == argumentsIncludingReceiver.size)

                val indicesOfErroneousParameters = ArrayList<Int>(argumentsIncludingReceiver.size)
                unification = argumentsIncludingReceiver
                    .zip(rightSideTypes)
                    .foldIndexed(unification) { parameterIndex, carryUnification, (argument, parameterType) ->
                        val unificationAfterParameter = parameterType.unify(argument.type!!, argument.declaration.span, carryUnification)
                        if (unificationAfterParameter.getErrorsNotIn(carryUnification).any()) {
                            indicesOfErroneousParameters.add(parameterIndex)
                        }
                        unificationAfterParameter
                    }

                val inapplicableReason = when (val inspectResult = candidateFilter?.inspect(candidateFn)) {
                    null, CandidateFilter.Result.Applicable -> null
                    is CandidateFilter.Result.Inapplicable -> inspectResult.reason
                }

                OverloadCandidateEvaluation(
                    candidateFn,
                    unification,
                    returnTypeWithVariables?.instantiateFreeVariables(unification),
                    indicesOfErroneousParameters,
                    inapplicableReason,
                )
            }
            .toList()
    }

    private var nothrowBoundary: NothrowViolationDiagnostic.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        this.nothrowBoundary = boundary
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
                    if (targetFn.throwBehavior != SideEffectPrediction.NEVER) {
                        diagnosis.nothrowViolatingInvocation(this, nothrowBoundary)
                    }
                }
            }
        }
    }

    /** so that identity remains constant throughout visits to this instance */
    private val asImpurity: ImpureInvocation? by lazy {
        seanHelper.requirePhase2Done()
        val functionToInvoke = this.functionToInvoke ?: return@lazy null
        if (BoundFunction.Purity.PURE.contains(functionToInvoke.purity)) {
            return@lazy null
        }

        ImpureInvocation(
            this,
            functionToInvoke,
        )
    }
    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase2Done()

        receiverExpression?.visitReadsBeyond(boundary, visitor)
        valueArguments.forEach { it.visitReadsBeyond(boundary, visitor) }

        asImpurity?.let { impurity ->
            if (!BoundFunction.Purity.PURE.contains(impurity.functionToInvoke.purity)) {
                visitor.visit(impurity)
            }
        }
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase2Done()

        receiverExpression?.visitWritesBeyond(boundary, visitor)
        valueArguments.forEach { it.visitWritesBeyond(boundary, visitor) }

        asImpurity?.let { impurity ->
            if (!BoundFunction.Purity.READONLY.contains(impurity.functionToInvoke.purity)) {
                visitor.visit(impurity)
            }
        }
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
            if (!BoundFunction.Purity.PURE.contains(localDispatchedFunction.purity)) {
                return false
            }
            val receiverIsConstant = receiverExpression?.isCompileTimeConstant ?: true
            return receiverIsConstant && valueArguments.all { it.isCompileTimeConstant }
        }

    private fun buildBackendIrInvocation(
        arguments: List<IrTemporaryValueReference>,
        landingpad: IrInvocationExpression.Landingpad?,
    ): IrExpression {
        val isCallOnInterfaceType = (receiverExpression?.type as? RootResolvedTypeReference)?.baseType?.kind == BoundBaseType.Kind.INTERFACE
        val fn = functionToInvoke!!
        val returnType = type!!.toBackendIr()
        val irResolvedTypeArgs = chosenOverload!!.unification.bindings.entries
            .associate { (typeVar, binding) -> typeVar.parameter.name to binding.toBackendIr() }

        // TODO: doesn't this lead to static dispatch when calling methods on generic types??
        if (fn is BoundMemberFunction && fn.isVirtual && isCallOnInterfaceType) {
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
            type!!.toBackendIr(),
            landingpad,
        )
    }

    override fun toBackendIrExpression(): IrExpression {
        return buildGenericInvocationLikeIr(
            context,
            declaration.span,
            listOfNotNull(receiverExceptReferringType) + valueArguments,
            ::buildBackendIrInvocation,
            assumeNothrow = functionToInvoke!!.attributes.isDeclaredNothrow,
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        return buildGenericInvocationLikeIr(
            context,
            declaration.span,
            listOfNotNull(receiverExceptReferringType) + valueArguments,
            ::buildBackendIrInvocation,
            { listOf(IrDropStrongReferenceStatementImpl(it)) },
            assumeNothrow = functionToInvoke!!.attributes.isDeclaredNothrow,
        ).code
    }

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
) {
    val hasErrors = inapplicableReason != null || unification.diagnostics.any { it.severity >= Diagnostic.Severity.ERROR }
}

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
 * common base for [buildGenericInvocationLikeIr] and [buildNothrowInvocationLikeIr]
 */
private fun buildInvocationLikeIrInternal(
    boundArgumentExprs: List<BoundExpression<*>>,
    buildActualCall: (arguments: List<IrTemporaryValueReference>, argumentsCleanupCode: List<IrExecutable>) -> IrExpression,
    buildResultCleanup: (IrTemporaryValueReference) -> List<IrExecutable>,
): IrImplicitEvaluationExpression {
    val prepareArgumentsCode = ArrayList<IrExecutable>(boundArgumentExprs.size * 2)
    val argumentTemporaries = ArrayList<IrCreateTemporaryValue>(boundArgumentExprs.size)
    val cleanUpArgumentsCode = ArrayList<IrExecutable>(boundArgumentExprs.size)

    for (boundArgumentExpr in boundArgumentExprs) {
        val irExpr = boundArgumentExpr.toBackendIrExpression()
        val temporary = IrCreateTemporaryValueImpl(irExpr)
        argumentTemporaries.add(temporary)
        prepareArgumentsCode.add(temporary)
        if (!boundArgumentExpr.isEvaluationResultAnchored) {
            if (!boundArgumentExpr.isEvaluationResultReferenceCounted) {
                // refcount to keep alive during the evaluation of subsequent temporaries
                prepareArgumentsCode.add(IrCreateStrongReferenceStatementImpl(temporary))
            }
            if (boundArgumentExpr.isEvaluationResultReferenceCounted) {
                // use of the temporary is over after the call, drop the reference
                cleanUpArgumentsCode.add(IrDropStrongReferenceStatementImpl(temporary))
            }
        } // else: if anchored we don't need to refcount the temporary
    }

    val returnValueTemporary = IrCreateTemporaryValueImpl(
        buildActualCall(
            argumentTemporaries.map { IrTemporaryValueReferenceImpl(it) },
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
        boundArgumentExprs,
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
    return buildInvocationLikeIrInternal(
        boundArgumentExprs,
        { args, argsCleanupCode ->
            val landingpad = if (assumeNothrow) null else {
                val cleanupCode = argsCleanupCode + context.getExceptionHandlingLocalDeferredCode().map { it.toBackendIrStatement() }.toList()
                val landingpadContext = MutableExecutionScopedCTContext.deriveFrom(context)
                val throwableVar = VariableDeclaration(
                    invocationLocation,
                    null,
                    null,
                    null,
                    IdentifierToken(
                        landingpadContext.findInternalVariableName("t"),
                        invocationLocation
                    ),
                    TypeReference(IdentifierToken("Throwable", invocationLocation)),
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
                    context.getDeferredCodeForThrow()
                        .map { it.toBackendIrStatement() }
                        .toList()
                    +
                    listOf(IrThrowStatementImpl(IrTemporaryValueReferenceImpl(exceptionTemporary)))
                )
                val catchOrRethrow: List<IrExecutable> = if (context.hasExceptionHandler) {
                    val isError = IrCreateTemporaryValueImpl(buildInstanceOf(
                        landingpadContext.swCtx,
                        IrTemporaryValueReferenceImpl(exceptionTemporary),
                        landingpadContext.swCtx.error,
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