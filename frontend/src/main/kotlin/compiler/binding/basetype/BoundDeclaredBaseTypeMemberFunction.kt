package compiler.binding.basetype

import compiler.ast.BaseTypeMemberFunctionDeclaration
import compiler.ast.FunctionDeclaration
import compiler.ast.type.NamedTypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.externalMemberFunction
import compiler.diagnostic.functionDoesNotOverride
import compiler.diagnostic.illegalFunctionBody
import compiler.diagnostic.incompatibleReturnTypeOnOverride
import compiler.diagnostic.missingFunctionBody
import compiler.diagnostic.nonVirtualMemberFunctionWithReceiver
import compiler.diagnostic.overrideAccessorDeclarationMismatch
import compiler.diagnostic.overrideAddsSideEffects
import compiler.diagnostic.overrideDropsNothrow
import compiler.diagnostic.overrideRestrictsVisibility
import compiler.diagnostic.overridingParameterExtendsOwnership
import compiler.diagnostic.overridingParameterNarrowsType
import compiler.diagnostic.staticFunctionDeclaredOverride
import compiler.diagnostic.typeTupleToString
import compiler.diagnostic.undeclaredOverride
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.zip

class BoundDeclaredBaseTypeMemberFunction(
    parentContext: CTContext,
    functionRootContext: MutableExecutionScopedCTContext,
    declaration: FunctionDeclaration,
    attributes: BoundFunctionAttributeList,
    declaredTypeParameters: List<BoundTypeParameter>,
    parameters: BoundParameterList,
    body: Body?,
    getTypeDef: () -> BoundBaseType,
    private val impliedReceiverType: NamedTypeReference,
) : BoundBaseTypeEntry<BaseTypeMemberFunctionDeclaration>, BoundMemberFunction, BoundDeclaredFunction(
    parentContext,
    functionRootContext,
    declaration,
    attributes,
    declaredTypeParameters,
    parameters,
    body,
) {
    private val seanHelper = SeanHelper()

    override val declaredOnType by lazy(getTypeDef)
    override val ownerBaseType by lazy(getTypeDef)
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            declaredOnType.canonicalName,
            name,
        )
    }
    override var isVirtual: Boolean? by seanHelper.resultOfPhase1()
        private set
    override val isAbstract = !attributes.impliesNoBody && body == null

    override val visibility by lazy {
        attributes.visibility.coerceAtMost(declaredOnType.visibility)
    }

    override var overrides: Set<InheritedBoundMemberFunction>? by seanHelper.resultOfPhase1()
        private set

    override val roots: Set<BoundDeclaredBaseTypeMemberFunction>
        get() {
            return overrides
                ?.takeUnless { it.isEmpty() }
                ?.flatMap { it.roots }
                ?.toSet()
                ?: setOf(this)
        }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            super.semanticAnalysisPhase1(diagnosis)
            determineVirtuality(diagnosis)
            determineOverride(diagnosis)
        }
    }

    private fun determineVirtuality(diagnosis: Diagnosis) {
        val receiverParam = parameters.declaredReceiver ?: run {
            isVirtual = false
            return
        }
        val receiverType = receiverParam.typeAtDeclarationTime ?: run {
            isVirtual = null
            return
        }

        fun determineVirtualityInner(type: BoundTypeReference, diagnose: Boolean): Boolean {
            when (type) {
                is RootResolvedTypeReference -> {
                    val isVirtual = type.baseType == ownerBaseType
                    if (!isVirtual && diagnose) {
                        diagnosis.nonVirtualMemberFunctionWithReceiver(this, "the receiver type must be `${ownerBaseType.simpleName}`")
                    }
                    return isVirtual
                }
                is GenericTypeReference -> {
                    val isVirtual = determineVirtualityInner(type.parameter.bound, false)
                    if (!isVirtual && diagnose) {
                        diagnosis.nonVirtualMemberFunctionWithReceiver(this, "the bound of the receiver type parameter `${type.parameter.name}` must be `${ownerBaseType.simpleName}`")
                    }
                    return isVirtual
                }
                is BoundIntersectionTypeReference -> {
                    val isVirtual = type.components.any { determineVirtualityInner(it, false) }
                    if (!isVirtual && diagnose) {
                        diagnosis.nonVirtualMemberFunctionWithReceiver(this, "one of the components of the receiver type must be `${ownerBaseType.simpleName}`")
                    }
                    return isVirtual
                }
                else -> {
                    if (diagnose) {
                        diagnosis.nonVirtualMemberFunctionWithReceiver(this, "the receiver type must be a named type or an intersection type")
                    }
                    return false
                }
            }
        }

        isVirtual = determineVirtualityInner(receiverType, true)
    }

    private fun determineOverride(diagnosis: Diagnosis) {
        val isDeclaredOverride = attributes.firstOverrideAttribute != null
        if (isDeclaredOverride && !declaresReceiver) {
            diagnosis.staticFunctionDeclaredOverride(this)
            overrides = emptySet()
            return
        }

        val superFns = findOverriddenFunctions(diagnosis)
        if (isDeclaredOverride) {
            if (superFns.none()) {
                diagnosis.functionDoesNotOverride(this)
            }
        } else {
            if (superFns.any()) {
                val supertype = superFns.first().declaredOnType
                diagnosis.undeclaredOverride(this, supertype)
            }
        }

        overrides = superFns.filter { it.isVirtual ?: true }.toSet()
    }

    private fun findOverriddenFunctions(diagnosis: Diagnosis): Sequence<InheritedBoundMemberFunction> {
        val selfParameterTypes = parameterTypes
            .drop(1) // ignore receiver
            .asElementNotNullable()
            ?: return emptySequence()

        declaredOnType.superTypes.semanticAnalysisPhase1(diagnosis)
        return declaredOnType.superTypes.inheritedMemberFunctions
            .asSequence()
            .filter { it.canonicalName.simpleName == this.name }
            .filter { it.parameters.parameters.size == this.parameters.parameters.size }
            .filter { potentialSuperFn ->
                val potentialSuperFnParamTypes = potentialSuperFn.parameterTypes
                    .drop(1) // ignore receiver
                    .asElementNotNullable()
                    ?: return@filter false

                selfParameterTypes.asSequence().zip(potentialSuperFnParamTypes.asSequence())
                    .all { (selfParamType, superParamType) -> superParamType == selfParamType }
            }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            super.semanticAnalysisPhase2(diagnosis)
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            super.semanticAnalysisPhase3(diagnosis)

            if (attributes.externalAttribute != null) {
                diagnosis.externalMemberFunction(this)
            }

            if (body != null) {
                if (attributes.impliesNoBody) {
                    diagnosis.illegalFunctionBody(declaration)
                }
            } else {
                if (!attributes.impliesNoBody && !declaredOnType.kind.memberFunctionsAbstractByDefault) {
                    diagnosis.missingFunctionBody(declaration)
                }
            }

            for (inheritedFn in overrides ?: emptyList()) {
                if (!inheritedFn.purity.contains(this.purity)) {
                    diagnosis.overrideAddsSideEffects(this, inheritedFn)
                }
                if (inheritedFn.attributes.isDeclaredNothrow && !this.attributes.isDeclaredNothrow) {
                    diagnosis.overrideDropsNothrow(this, inheritedFn)
                }
                if (inheritedFn.visibility.isPossiblyBroaderThan(visibility) && declaredOnType.visibility.isPossiblyBroaderThan(visibility)) {
                    diagnosis.overrideRestrictsVisibility(this, inheritedFn)
                }
                if (inheritedFn.attributes.firstAccessorAttribute != attributes.firstAccessorAttribute) {
                    diagnosis.overrideAccessorDeclarationMismatch(this, inheritedFn)
                }

                for ((inheritedFnParam, overrideFnParam, paramOnSupertypeFn) in zip(inheritedFn.parameters.parameters, this.parameters.parameters, inheritedFn.supertypeMemberFn.parameters.parameters)) {
                    if (!overrideFnParam.ownershipAtDeclarationTime.canOverride(inheritedFnParam.ownershipAtDeclarationTime)) {
                        diagnosis.overridingParameterExtendsOwnership(overrideFnParam, paramOnSupertypeFn)
                    }
                }

                val declaredReceiverType = this.receiverType
                val superReceiverType = inheritedFn.receiverType?.instantiateAllParameters(inheritedFn.supertypeAsDeclared.inherentTypeBindings)
                if (declaredReceiverType != null && superReceiverType != null) {
                    val expectedReceiverType = superReceiverType.intersect(functionRootContext.resolveType(this.impliedReceiverType))
                    expectedReceiverType
                        .evaluateAssignabilityTo(declaredReceiverType, declaredReceiverType.span ?: Span.UNKNOWN)
                        ?.let { narrowReceiverError ->
                            diagnosis.overridingParameterNarrowsType(
                                this.parameters.declaredReceiver!!,
                                inheritedFn.supertypeMemberFn.parameters.declaredReceiver!!,
                                narrowReceiverError
                            )
                        }
                }
                /*
                currently, the other parameters need not be checked, because the override semantics require that the
                types are exactly the same
                 */

                val selfReturnType = returnType
                val superReturnType = inheritedFn.returnType
                if (selfReturnType != null && superReturnType != null) {
                    selfReturnType
                        .evaluateAssignabilityTo(superReturnType, declaration.parsedReturnType?.span ?: declaredAt)
                        ?.let { wideReturnTypeError ->
                            diagnosis.incompatibleReturnTypeOnOverride(this, inheritedFn, wideReturnTypeError)
                        }
                }
            }
        }
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        return visibility.validateAccessFrom(location, this, diagnosis)
    }

    override fun toStringForErrorMessage() = "member function $name"

    override fun toString(): String {
        var str = canonicalName.toString()
        if (declaredTypeParameters.isNotEmpty()) {
            str += declaredTypeParameters.joinToString(
                prefix = "<",
                separator = ", ",
                transform = { "${it.name} : ${it.bound.toString()}" },
                postfix = ">"
            )
        }
        str += parameters.parameters.joinToString(
            prefix = "(",
            separator = ", ",
            transform= { it.typeAtDeclarationTime.toString() },
            postfix = ") -> ",
        )
        str += returnType

        return str
    }

    private val backendIr by lazy { IrMemberFunctionImpl(this) }
    override fun toBackendIr(): IrMemberFunction = backendIr
}

private fun <T : Any> List<T?>.asElementNotNullable(): List<T>? {
    if (any { it == null }) {
        return null
    }

    @Suppress("UNCHECKED_CAST")
    return this as List<T>
}

private class IrMemberFunctionImpl(
    private val boundFn: BoundDeclaredBaseTypeMemberFunction,
) : IrMemberFunction {
    override val canonicalName = boundFn.canonicalName
    override val parameters = boundFn.parameters.parameters.map { it.backendIrDeclaration }
    override val declaresReceiver = boundFn.declaresReceiver
    override val returnType by lazy { boundFn.returnType!!.toBackendIr() }
    override val isExternalC = boundFn.attributes.externalAttribute?.ffiName?.value == "C"
    override val isNothrow = boundFn.attributes.isDeclaredNothrow
    override val body: IrCodeChunk? by lazy { boundFn.getFullBodyBackendIr() }
    override val overrides: Set<IrMemberFunction> by lazy { (boundFn.overrides ?: emptyList()).map { it.toBackendIr() }.toSet() }
    override val supportsDynamicDispatch = boundFn.isVirtual!!
    override val ownerBaseType by lazy { boundFn.declaredOnType.toBackendIr() }
    override val declaredAt = boundFn.declaredAt

    override fun toString() = "IrMemberFunction[$canonicalName${boundFn.parameterTypes.typeTupleToString()}]"
}