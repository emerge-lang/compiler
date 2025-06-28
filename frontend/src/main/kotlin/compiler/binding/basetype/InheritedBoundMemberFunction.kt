package compiler.binding.basetype

import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrFullyInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName

class InheritedBoundMemberFunction(
    val supertypeMemberFn: BoundMemberFunction,
    override val ownerBaseType: BoundBaseType,
    /** The supertype that is being inherited from, as it appears in [BoundSupertypeDeclaration] */
    val supertypeAsDeclared: RootResolvedTypeReference,
) : BoundMemberFunction by supertypeMemberFn {
    init {
        check(supertypeMemberFn.declaresReceiver) {
            "Inheriting a member function without receiver - that's nonsensical!"
        }
    }

    private val functionContext = supertypeMemberFn.context as? ExecutionScopedCTContext
        ?: MutableExecutionScopedCTContext.functionRootIn(supertypeMemberFn.context)
    override val context = ownerBaseType.context

    override val roots get()= supertypeMemberFn.roots

    override val canonicalName = CanonicalElementName.Function(
        ownerBaseType.canonicalName,
        supertypeMemberFn.name,
    )

    // this is intentional - as long as not overridden, this info is truthful & accurate
    override val declaredOnType get()= supertypeMemberFn.declaredOnType

    private val relocatedReceiverParameter: VariableDeclaration = run {
        val inheritedReceiverParameter = supertypeMemberFn.parameters.declaredReceiver!!
        // it is important that this location comes from the subtype
        // this is necessary, so the access checks pass on module-private or less visible subtypes
        inheritedReceiverParameter.declaration.copy(
            declaredAt = ownerBaseType.declaration.declaredAt.deriveGenerated()
        )
    }

    /**
     * If the [supertypeAsDeclared] does not conform to the [BoundMemberFunction.receiverType], this function is not
     * actually inherited ("inheritances is precluded"). [inheritancePreclusionReason] holds the result of this
     * conformity check ([BoundTypeReference.evaluateAssignabilityTo]), available after [semanticAnalysisPhase2].
     */
    var inheritancePreclusionReason: Diagnostic? = null

    override val parameters: BoundParameterList = run {
        val translatedParams = supertypeMemberFn.parameters.parameters
            .drop(1)
            .map { boundSuperParam ->
                val translatedtype = boundSuperParam.typeAtDeclarationTime?.instantiateAllParameters(supertypeAsDeclared.inherentTypeBindings)
                    ?: return@map boundSuperParam.declaration

                boundSuperParam.declaration.copy(type = translatedtype.asAstReference())
            }
        ParameterList(
            listOf(relocatedReceiverParameter) + translatedParams
        ).bindTo(functionContext)
    }

    override val receiverType = parameters.declaredReceiver!!.typeAtDeclarationTime
    override val returnType get()= supertypeMemberFn.returnType?.instantiateAllParameters(supertypeAsDeclared.inherentTypeBindings)

    // semantic analysis is not really needed here; the super function will have its sean functions invoked, too
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        parameters.semanticAnalysisPhase1(diagnosis)
        parameters.parameters.forEach { it.semanticAnalysisPhase1(diagnosis) }

        val superReceiverType = supertypeMemberFn.parameters.declaredReceiver!!.typeAtDeclarationTime ?: return
        inheritancePreclusionReason = supertypeAsDeclared
            .defaultMutabilityTo(superReceiverType.mutability)
            .evaluateAssignabilityTo(superReceiverType, supertypeAsDeclared.span ?: ownerBaseType.declaration.declaredAt)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        parameters.parameters.forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        parameters.parameters.forEach { it.semanticAnalysisPhase3(diagnosis) }
    }

    private val backendIr by lazy {
        IrFullyInheritedMemberFunctionImpl(
            { ownerBaseType.toBackendIr() },
            supertypeMemberFn.toBackendIr(),
            canonicalName
        )
    }
    override fun toBackendIr(): IrInheritedMemberFunction = backendIr

    override fun toString(): String {
        return "$canonicalName(${parameters.parameters.joinToString(separator = ", ", transform = { it.typeAtDeclarationTime.toString() })}) -> $returnType"
    }

    companion object {
        /**
         * @return the (in-)direct common override (see [compiler.binding.basetype.InheritedBoundMemberFunction.overrides])
         * across all of [inheritedFns] as declared on the most concrete receiver type possible, or `null` if no such
         * function exists.
         */
        fun closestCommonOverriddenFunction(inheritedFns: Iterable<InheritedBoundMemberFunction>): BoundMemberFunction? {
            val closestCommonReceiverBaseType = inheritedFns
                .map { it.declaredOnType }
                .let(BoundBaseType::closestCommonSupertypeOf)

            val candidates = mutableSetOf<BoundMemberFunction>()
            for (fn in inheritedFns) {
                var hadCandidate = false
                for (candidate in fn.allOverrides) {
                    if (candidate.ownerBaseType == closestCommonReceiverBaseType) {
                        candidates.add(candidate)
                        hadCandidate = true
                    }
                }

                if (!hadCandidate) {
                    return null
                }
            }

            return candidates.singleOrNull()
        }
    }
}

private val BoundMemberFunction.allOverrides: Sequence<BoundMemberFunction> get() = sequence {
    val overriddenOrParent = if (this@allOverrides is InheritedBoundMemberFunction) setOf(supertypeMemberFn) else overrides!!
    for (overridden in overriddenOrParent) {
        yield(overridden)
        yieldAll(overridden.allOverrides)
    }
}

private class IrFullyInheritedMemberFunctionImpl(
    private val getInheritingBaseType: () -> IrBaseType,
    override val superFunction: IrMemberFunction,
    override val canonicalName: CanonicalElementName.Function,
) : IrFullyInheritedMemberFunction, IrMemberFunction by superFunction {
    override val ownerBaseType: IrBaseType get() = getInheritingBaseType()
}