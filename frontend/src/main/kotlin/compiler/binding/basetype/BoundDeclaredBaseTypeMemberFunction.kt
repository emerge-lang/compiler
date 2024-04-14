package compiler.binding.basetype

import compiler.ast.BaseTypeMemberFunctionDeclaration
import compiler.ast.FunctionDeclaration
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.isAssignableTo
import compiler.lexer.SourceLocation
import compiler.reportings.IncompatibleReturnTypeOnOverrideReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

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
    override val declaredOnType by lazy(getTypeDef)
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            declaredOnType.canonicalName,
            name,
        )
    }
    override val isVirtual get() = declaresReceiver

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = super.semanticAnalysisPhase3().toMutableList()
        validateOverride(reportings)

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

        return reportings
    }

    private fun validateOverride(reportings: MutableCollection<Reporting>) {
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

        if (!isDeclaredOverride) {
            return
        }

        val superFn = superFns.singleOrNull()?.second ?: return
        returnType?.let { overriddenReturnType ->
            superFn.returnType?.let { superReturnType ->
                overriddenReturnType.evaluateAssignabilityTo(superReturnType, overriddenReturnType.sourceLocation ?: SourceLocation.UNKNOWN)
                    ?.let {
                        reportings.add(IncompatibleReturnTypeOnOverrideReporting(declaration, it))
                    }
            }
        }
    }

    private fun findOverriddenFunction(): Collection<Pair<BaseType, BoundFunction>> {
        val selfParameterTypes = parameterTypes.asElementNotNullable()
            ?: return emptySet()

        declaredOnType.superTypes.semanticAnalysisPhase3()
        return declaredOnType.superTypes.inheritedMemberFunctions
            .asSequence()
            .filter { it.canonicalName.simpleName == this.name }
            .filter { it.parameterCount == this.parameters.parameters.size }
            .flatMap { it.overloads }
            .filter { potentialSuperFn ->
                val potentialSuperFnParamTypes = potentialSuperFn.parameterTypes.asElementNotNullable()
                    ?: return@filter false
                selfParameterTypes.asSequence().zip(potentialSuperFnParamTypes.asSequence())
                    .drop(1) // ignore receiver
                    .all { (selfParamType, superParamType) -> superParamType.isAssignableTo(selfParamType) }
            }
            .map { superFn ->
                val supertype = (superFn as BoundDeclaredBaseTypeMemberFunction).declaredOnType
                Pair(supertype, superFn)
            }
            .toList()
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "member function $name"
}

private fun <T : Any> List<T?>.asElementNotNullable(): List<T>? {
    if (any { it == null }) {
        return null
    }

    @Suppress("UNCHECKED_CAST")
    return this as List<T>
}