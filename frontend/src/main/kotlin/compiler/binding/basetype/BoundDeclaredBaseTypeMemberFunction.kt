package compiler.binding.basetype

import compiler.ast.BaseTypeMemberFunctionDeclaration
import compiler.ast.FunctionDeclaration
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.isAssignableTo
import compiler.lexer.SourceLocation
import compiler.reportings.IncompatibleReturnTypeOnOverrideReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction

class BoundDeclaredBaseTypeMemberFunction(
    functionRootContext: CTContext,
    declaration: FunctionDeclaration,
    attributes: BoundFunctionAttributeList,
    declaredTypeParameters: List<BoundTypeParameter>,
    parameters: BoundParameterList,
    body: Body?,
    getTypeDef: () -> BoundBaseTypeDefinition,
) : BoundBaseTypeEntry<BaseTypeMemberFunctionDeclaration>, BoundMemberFunction, BoundDeclaredFunction(
    functionRootContext,
    declaration,
    attributes,
    declaredTypeParameters,
    parameters,
    body,
) {
    private val seanHelper = SeanHelper()

    override val declaredOnType by lazy(getTypeDef)
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            declaredOnType.canonicalName,
            name,
        )
    }
    override val isVirtual get() = declaresReceiver
    override val isAbstract = !attributes.impliesNoBody && body == null

    override var overrides: InheritedBoundMemberFunction? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            super.semanticAnalysisPhase1()
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = super.semanticAnalysisPhase2().toMutableList()
            determineOverride(reportings)
            return@phase2 reportings
        }
    }

    private fun determineOverride(reportings: MutableCollection<Reporting>) {
        val isDeclaredOverride = attributes.firstOverrideAttribute != null
        if (isDeclaredOverride && !declaresReceiver) {
            reportings.add(Reporting.staticFunctionDeclaredOverride(this))
            return
        }

        val superFns = findOverriddenFunction()
        if (isDeclaredOverride) {
            when (superFns.size) {
                0 -> reportings.add(Reporting.functionDoesNotOverride(this))
                1 -> { /* awesome, things are as they should be */ }
                else -> reportings.add(Reporting.ambiguousOverride(this))
            }
        } else {
            when (superFns.size) {
                0 ->  { /* awesome, things are as they should be */ }
                else -> {
                    val supertype = superFns.first().first
                    reportings.add(Reporting.undeclaredOverride(this, supertype))
                }
            }
        }

        val superFn = superFns.singleOrNull()?.second ?: return
        overrides = superFn

        returnType?.let { overriddenReturnType ->
            superFn.returnType?.let { superReturnType ->
                overriddenReturnType.evaluateAssignabilityTo(superReturnType, overriddenReturnType.sourceLocation ?: SourceLocation.UNKNOWN)
                    ?.let {
                        reportings.add(IncompatibleReturnTypeOnOverrideReporting(declaration, it))
                    }
            }
        }
    }

    private fun findOverriddenFunction(): Collection<Pair<BaseType, InheritedBoundMemberFunction>> {
        val selfParameterTypes = parameterTypes
            .drop(1) // ignore receiver
            .asElementNotNullable()
            ?: return emptySet()

        declaredOnType.superTypes.semanticAnalysisPhase2()
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
                    .all { (selfParamType, superParamType) -> superParamType.isAssignableTo(selfParamType) }
            }
            .map { superFn ->
                val supertype = superFn.declaredOnType
                Pair(supertype, superFn)
            }
            .toList()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = super.semanticAnalysisPhase3().toMutableList()

            if (attributes.externalAttribute != null) {
                reportings.add(Reporting.externalMemberFunction(this))
            }

            if (body != null) {
                if (attributes.impliesNoBody) {
                    reportings.add(Reporting.illegalFunctionBody(declaration))
                }
            } else {
                if (!attributes.impliesNoBody && !declaredOnType.kind.memberFunctionsAbstractByDefault) {
                    reportings.add(Reporting.missingFunctionBody(declaration))
                }
            }

            return@phase3 reportings
        }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "member function $name"

    override fun toString(): String {
        return "$canonicalName(${parameters.parameters.joinToString(separator = ", ", transform= { it.typeAtDeclarationTime.toString() })}) -> $returnType"
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
    override val returnType by lazy { boundFn.returnType!!.toBackendIr() }
    override val isExternalC = boundFn.attributes.externalAttribute?.ffiName?.value == "C"
    override val body: IrCodeChunk? by lazy { boundFn.body?.toBackendIr() }
    override val overrides: IrMemberFunction? by lazy { boundFn.overrides?.toBackendIr() }
    override val supportsDynamicDispatch = boundFn.isVirtual
    override val declaredOn by lazy { boundFn.declaredOnType.toBackendIr() }
}