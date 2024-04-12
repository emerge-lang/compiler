package compiler.binding.basetype

import compiler.ast.ClassEntryDeclaration
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunction
import compiler.binding.DefinitionWithVisibility
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.isAssignableTo
import compiler.lexer.SourceLocation
import compiler.reportings.IncompatibleReturnTypeOnOverrideReporting
import compiler.reportings.Reporting

class BoundBaseTypeMemberFunction(
    override val context: CTContext,
    override val declaration: ClassEntryDeclaration,
    val functionInstance: BoundDeclaredFunction,
    getClassDef: () -> BoundBaseTypeDefinition,
) : BoundBaseTypeEntry<ClassEntryDeclaration>, DefinitionWithVisibility {
    private val classDef by lazy(getClassDef)
    val name = functionInstance.name
    override val visibility get()= functionInstance.attributes.visibility

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return functionInstance.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return functionInstance.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(functionInstance.semanticAnalysisPhase3())
        validateOverride(reportings)

        return reportings
    }

    private fun validateOverride(reportings: MutableCollection<Reporting>) {
        val isDeclaredOverride = functionInstance.attributes.firstOverrideAttribute != null
        if (isDeclaredOverride && !functionInstance.declaresReceiver) {
            reportings.add(Reporting.staticFunctionDeclaredOverride(functionInstance))
            return
        }

        val superFns = findOverriddenFunction()
        if (isDeclaredOverride) {
            when (superFns.size) {
                0 -> reportings.add(Reporting.functionDoesNotOverride(functionInstance))
                1 -> { /* awesome, things are as they should be */ }
                else -> reportings.add(Reporting.ambiguousOverride(functionInstance))
            }
        } else {
            when (superFns.size) {
                0 ->  { /* awesome, things are as they should be */ }
                else -> {
                    val supertype = superFns.first().first
                    reportings.add(Reporting.undeclaredOverride(functionInstance, supertype))
                }
            }
        }

        if (!isDeclaredOverride) {
            return
        }

        val superFn = superFns.singleOrNull()?.second ?: return
        functionInstance.returnType?.let { overriddenReturnType ->
            superFn.returnType?.let { superReturnType ->
                overriddenReturnType.evaluateAssignabilityTo(superReturnType, overriddenReturnType.sourceLocation ?: SourceLocation.UNKNOWN)
                    ?.let {
                        reportings.add(IncompatibleReturnTypeOnOverrideReporting(functionInstance.declaration, it))
                    }
            }
        }
    }

    private fun findOverriddenFunction(): Collection<Pair<BaseType, BoundFunction>> {
        val selfParameterTypes = functionInstance.parameterTypes.asElementNotNullable()
            ?: return emptySet()

        return classDef.superTypes
            .flatMap { supertype ->
                val potentialSuperFns = supertype.resolveMemberFunction(functionInstance.name)
                    .filter { it.parameterCount == functionInstance.parameters.parameters.size }
                    .flatMap { it.overloads }

                potentialSuperFns.map {
                    Pair(supertype, it)
                }
            }
            .filter { (_, potentialSuperFn) ->
                val potentialSuperFnParamTypes = potentialSuperFn.parameterTypes.asElementNotNullable()
                    ?: return@filter false
                selfParameterTypes.asSequence().zip(potentialSuperFnParamTypes.asSequence())
                    .drop(1) // ignore receiver
                    .all { (selfParamType, superParamType) -> superParamType.isAssignableTo(selfParamType) }
            }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return functionInstance.visibility.validateAccessFrom(location, this)
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