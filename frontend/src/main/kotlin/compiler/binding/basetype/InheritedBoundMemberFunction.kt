package compiler.binding.basetype

import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUnification
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.lexer.Span
import compiler.util.Either
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

    private val rawSuperFnContext = supertypeMemberFn.context as? ExecutionScopedCTContext
        ?: MutableExecutionScopedCTContext.functionRootIn(supertypeMemberFn.context)
    override val context = ownerBaseType.context
    private val functionContext = object : ExecutionScopedCTContext by rawSuperFnContext {
        override fun resolveType(ref: TypeReference, fromOwnFileOnly: Boolean): BoundTypeReference {
            if (ref === narrowedReceiverParameter.type) {
                return ownerBaseType.typeRootContext.resolveType(ref, fromOwnFileOnly)
            }

            return rawSuperFnContext.resolveType(ref, fromOwnFileOnly)
        }
    }

    override val canonicalName = CanonicalElementName.Function(
        ownerBaseType.canonicalName,
        supertypeMemberFn.name,
    )

    // this is intentional - as long as not overridden, this info is truthful & accurate
    override val declaredOnType get()= supertypeMemberFn.declaredOnType

    /**
     * Iff the [supertypeAsDeclared] is not assignable to the declared receiver of the super function,
     * this variable will hold the details for that.
     *
     * This could happen e.g. in this case:
     *
     *     interface S<T> {
     *       fn foo(self: S<S32>) {} // defined only when T = S32
     *     }
     *     class D : S<String> {
     *       // cannot inherit ::foo, because T != S32; foo could never be invoked on instances of D
     *     }
     */
    private val supertypeDeclarationAndReceiverTypeConflict: Diagnostic?
    private val narrowedReceiverType: RootResolvedTypeReference
    init {
        when (val nrtr = buildNarrowedReceiverType()) {
            is Either.This -> {
                supertypeDeclarationAndReceiverTypeConflict = null
                narrowedReceiverType = nrtr.value
            }
            is Either.That -> {
                // TODO: handle this situation when this function is attempted to be overwritten
                supertypeDeclarationAndReceiverTypeConflict = nrtr.value
                narrowedReceiverType = context.swCtx.nothing.baseReference.withMutability(supertypeMemberFn.receiverType?.mutability ?: TypeMutability.READONLY)
            }
        }
    }

    private val narrowedReceiverParameter: VariableDeclaration = run {
        val inheritedReceiverParameter = supertypeMemberFn.parameters.declaredReceiver!!
        // it is important that this location comes from the subtype
        // this is necessary so the access checks pass on module-private or less visible subtypes
        val sourceLocation = ownerBaseType.declaration.declaredAt.deriveGenerated()
        VariableDeclaration(
            sourceLocation,
            null,
            null,
            inheritedReceiverParameter.declaration.ownership,
            inheritedReceiverParameter.declaration.name,
            narrowedReceiverType.asAstReference(),
            null,
        )
    }

    override val parameters: BoundParameterList = run {
        val translatedParams = supertypeMemberFn.parameters.parameters
            .drop(1)
            .map { boundSuperParam ->
                val translatedtype = boundSuperParam.typeAtDeclarationTime?.instantiateAllParameters(supertypeAsDeclared.inherentTypeBindings)
                    ?: return@map boundSuperParam.declaration

                boundSuperParam.declaration.copy(type = translatedtype.asAstReference())
            }
        ParameterList(
            listOf(narrowedReceiverParameter) + translatedParams
        ).bindTo(functionContext)
    }

    override val receiverType = narrowedReceiverType
    override val returnType get()= supertypeMemberFn.returnType?.instantiateAllParameters(supertypeAsDeclared.inherentTypeBindings)

    // semantic analysis is not really needed here; the super function will have its sean functions invoked, too
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        parameters.semanticAnalysisPhase1(diagnosis)
        parameters.parameters.forEach { it.semanticAnalysisPhase1(diagnosis) }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        parameters.parameters.forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        parameters.parameters.forEach { it.semanticAnalysisPhase3(diagnosis) }
    }

    private fun buildNarrowedReceiverType(): Either<RootResolvedTypeReference, Diagnostic> {
        val superReceiverType = supertypeMemberFn.receiverType
        if (superReceiverType == null || ownerBaseType.typeParameters.isNullOrEmpty()) {
            return Either.This(
                ownerBaseType.baseReference
                    .withMutability(supertypeMemberFn.receiverType?.mutability ?: TypeMutability.READONLY)
            )
        }

        val superReceiverWithRightParams = superReceiverType.instantiateAllParameters(supertypeAsDeclared.inherentTypeBindings)
        val varReceiver = superReceiverWithRightParams.withTypeVariables(ownerBaseType.typeParameters)
        val emptyUnification = TypeUnification.forInferenceOf(ownerBaseType.typeParameters)
        val unification = supertypeAsDeclared.unify(varReceiver, Span.UNKNOWN, emptyUnification)
        unification.getErrorsNotIn(emptyUnification)
            .firstOrNull()
            ?.let { return Either.That(it) }

        val arguments = ownerBaseType.typeParameters.map {
            val argType = unification.getFinalValueFor(it)
            BoundTypeArgument(context, TypeArgument(TypeVariance.UNSPECIFIED, argType.asAstReference()), TypeVariance.UNSPECIFIED, argType)
        }
        return Either.This(RootResolvedTypeReference(
            context,
            NamedTypeReference(
                ownerBaseType.simpleName,
                TypeReference.Nullability.of(superReceiverType),
                superReceiverType.mutability,
                null,
                arguments.map { it.astNode },
                supertypeMemberFn.parameters.declaredReceiver!!.declaration.type?.span
                    ?: supertypeMemberFn.parameters.declaredReceiver!!.declaration.name.span
            ),
            ownerBaseType,
            arguments,
        ))
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
}

private class IrFullyInheritedMemberFunctionImpl(
    private val getInheritingBaseType: () -> IrBaseType,
    override val superFunction: IrMemberFunction,
    override val canonicalName: CanonicalElementName.Function,
) : IrFullyInheritedMemberFunction, IrMemberFunction by superFunction {
    override val ownerBaseType: IrBaseType get() = getInheritingBaseType()
}