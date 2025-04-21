package compiler.binding.context

import compiler.binding.AccessorKind
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.PackageContext.TypeBranch.Companion.groupTypeBranches
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isAssignableTo
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.duplicateBaseTypes
import compiler.diagnostic.getterAndSetterWithDifferentType
import compiler.diagnostic.multipleAccessorsOnPackage
import io.github.tmarsteel.emerge.common.CanonicalElementName

class PackageContext(
    val moduleContext: ModuleContext,
    val packageName: CanonicalElementName.Package,
) : SemanticallyAnalyzable {
    val sourceFiles: Sequence<SourceFile> = sequence {
        yieldAll(moduleContext.sourceFiles)
    }.filter { it.packageName == packageName }

    val types: Sequence<BoundBaseType> get() {
        return sourceFiles
            .filter { it.packageName == packageName }
            .flatMap { it.context.types }
    }

    private val typeByNameCache = HashMap<String, BoundBaseType>()
    fun resolveBaseType(simpleName: String): BoundBaseType? {
        typeByNameCache[simpleName]?.let { return it }
        val type = types.find { it.simpleName == simpleName } ?: return null
        typeByNameCache[simpleName] = type
        return type
    }

    fun resolveVariable(simpleName: String): BoundVariable? {
        return sourceFiles
            .mapNotNull { it.context.resolveVariable(simpleName, true) }
            .firstOrNull()
    }

    private val overloadSetsBySimpleName: Map<String, Collection<BoundOverloadSet<*>>> by lazy {
        /*
        this HAS to be lazy, because:
        * it cannot be initialized together with the package context, as not all contents of the package are known at that point in time
        * it cannot be initialized in semanticAnalysisPhase1 because other code that depends on this package might do phase 1
          earlier; definitely the case for cyclic imports
         */
        sourceFiles
            .flatMap { it.context.functions }
            .groupBy { it.name }
            .mapValues { (name, overloads) ->
                overloads
                    .groupBy { it.parameters.parameters.size }
                    .map { (parameterCount, overloads) ->
                        BoundOverloadSet(overloads.first().canonicalName, parameterCount, overloads)
                    }
            }
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return overloadSetsBySimpleName.values
            .flatten()
            .forEach { it.semanticAnalysisPhase1(diagnosis) }
    }

    fun getTopLevelFunctionOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>> {
        return overloadSetsBySimpleName[simpleName] ?: emptySet()
    }

    val allToplevelFunctionOverloadSets: Sequence<BoundOverloadSet<*>> = sequence { yieldAll(overloadSetsBySimpleName.values) }.flatten()

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        sourceFiles.forEach { it.semanticAnalysisPhase2(diagnosis) }
        overloadSetsBySimpleName.values.flatten().forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        sourceFiles.forEach { it.semanticAnalysisPhase3(diagnosis) }
        overloadSetsBySimpleName.values.flatten().forEach { it.semanticAnalysisPhase3(diagnosis) }

        checkRulesAcrossAccessorsPhase3(diagnosis)

        types
            .groupBy { it.simpleName }
            .values
            .filter { it.size > 1 }
            .forEach { duplicateTypes ->
                diagnosis.duplicateBaseTypes(packageName, duplicateTypes)
            }
    }

    private fun checkRulesAcrossAccessorsPhase3(diagnosis: Diagnosis) {
        // getters need not be checked, because if multiple getters were forbidden here,
        // then it wouldn't be possible to declare the same virtual member on distinct types
        // however, if the same getter is defined for ambiguous/overlapping types, the
        // overload-set ambiguity will trigger and cause a diagnostic

        sourceFiles
            .flatMap { it.context.functions }
            .filter { it.attributes.firstAccessorAttribute != null }
            .groupBy { it.name }
            .forEach { (virtualMemberName, accessors) ->
                accessors
                    .groupTypeBranches { it.receiverType }
                    .forEach { branch ->
                        val getters = branch.elements.filter { it.attributes.firstAccessorAttribute!!.kind == AccessorKind.Read }
                        val setters = branch.elements.filter { it.attributes.firstAccessorAttribute!!.kind == AccessorKind.Write }

                        if (setters.size > 1) {
                            diagnosis.multipleAccessorsOnPackage(virtualMemberName, AccessorKind.Write, setters)
                            return@forEach
                        }

                        if (getters.size > 1) {
                            // this will be reported as an overload ambiguity on package level, no reason to dupe this diagnostic
                            return@forEach
                        }

                        val getter = getters.firstOrNull() ?: return@forEach
                        val getterType = AccessorKind.Read.extractMemberType(getter)
                        val setter = setters.firstOrNull() ?: return@forEach
                        val setterType = AccessorKind.Write.extractMemberType(setter)

                        if (getterType != null && setterType != null && getterType != setterType) {
                            diagnosis.getterAndSetterWithDifferentType(virtualMemberName, getter, setter)
                        }
                    }
            }
    }

    override fun equals(other: Any?): Boolean {
        return other != null && other::class == PackageContext::class && (other as PackageContext).packageName == this.packageName
    }

    override fun hashCode() = packageName.hashCode()

    /**
     * when looking at multiple things on package level that all associate to a type each,
     * sometimes the type hierarchy of all those elements needs to be inspected. This class helps
     * build that hierarchy
     */
    private class TypeBranch<T>(firstElement: T, firstType: BoundTypeReference) {
        private var leastSpecificTypeInBranch: BoundTypeReference = firstType
        private val _elements = mutableListOf<T>(firstElement)

        val elements: List<T> get() = _elements

        /**
         * If this element belongs to this branch, adds it and returns `true`.
         * @return `true` iff the element belongs to this branch and the branch was modified as a result of this call
         */
        fun tryAdd(element: T, withType: BoundTypeReference): Boolean {
            if (withType isAssignableTo leastSpecificTypeInBranch) {
                _elements.add(element)
                return true
            }
            if (leastSpecificTypeInBranch isAssignableTo withType) {
                leastSpecificTypeInBranch = withType
                _elements.add(element)
                return true
            }

            return false
        }

        companion object {
            fun <T> List<T>.groupTypeBranches(
                typeSelector: (T) -> BoundTypeReference?,
            ) : List<TypeBranch<T>> {
                val typeBranches = mutableListOf<TypeBranch<T>>()
                this
                    .mapNotNull {
                        val type = typeSelector(it) ?: return@mapNotNull null
                        it to type
                    }
                    .forEach { (element, type) ->
                        for (branch in typeBranches) {
                            if (branch.tryAdd(element, type)) {
                                return@forEach
                            }
                        }
                        typeBranches.add(TypeBranch(element, type))
                    }

                return typeBranches
            }
        }
    }
}