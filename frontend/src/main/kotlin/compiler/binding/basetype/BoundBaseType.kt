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

package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.AstCodeChunk
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.type.TypeReference
import compiler.binding.*
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.isAssignableTo
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span
import compiler.reportings.Reporting
import compiler.reportings.UnconventionalTypeNameReporting
import io.github.tmarsteel.emerge.backend.api.ir.*
import io.github.tmarsteel.emerge.common.CanonicalElementName
import kotlinext.duplicatesBy
import kotlinext.get
import java.util.*

class BoundBaseType(
    private val fileContext: CTContext,
    private val typeRootContext: CTContext,
    val kind: Kind,
    override val visibility: BoundVisibility,
    val typeParameters: List<BoundTypeParameter>?,
    val superTypes: BoundSupertypeList,
    override val declaration: BaseTypeDeclaration,
    val entries: List<BoundBaseTypeEntry<*>>,
) : BoundElement<BaseTypeDeclaration>, DefinitionWithVisibility {
    private val seanHelper = SeanHelper()

    override val context: CTContext = fileContext
    val canonicalName: CanonicalElementName.BaseType by lazy {
        CanonicalElementName.BaseType(context.sourceFile.packageName, declaration.name.value)
    }
    val simpleName: String = declaration.name.value
    val baseReference: RootResolvedTypeReference
        get() = RootResolvedTypeReference(
            TypeReference(this.simpleName),
            this,
            if (typeParameters.isNullOrEmpty()) null else throw InternalCompilerError("cannot use baseReference on types with parameters")
        )

    private val _memberVariables: MutableList<BoundBaseTypeMemberVariable> = entries.filterIsInstance<BoundBaseTypeMemberVariable>().toMutableList()
    val memberVariables: List<BoundBaseTypeMemberVariable> = _memberVariables
    val declaredConstructors: Sequence<BoundClassConstructor> = entries.asSequence().filterIsInstance<BoundClassConstructor>()
    val declaredDestructors: Sequence<BoundClassDestructor> = entries.asSequence().filterIsInstance<BoundClassDestructor>()

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    var constructor: BoundClassConstructor? = null
        private set

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    var destructor: BoundClassDestructor? = null
        private set

    private lateinit var allMemberFunctionOverloadSetsByName: Map<String, Collection<BoundOverloadSet<BoundMemberFunction>>>
    val memberFunctions: Collection<BoundOverloadSet<BoundMemberFunction>>
        get() {
            seanHelper.requirePhase1Done()
            if (!this::allMemberFunctionOverloadSetsByName.isInitialized) {
                return emptySet()
            }

            return allMemberFunctionOverloadSetsByName.values.flatten()
        }

    /** @return The member function overloads for the given name or an empty collection if no such member function is defined. */
    fun resolveMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        semanticAnalysisPhase1()
        if (!this::allMemberFunctionOverloadSetsByName.isInitialized) {
            return emptySet()
        }

        return allMemberFunctionOverloadSetsByName.getOrDefault(name, emptySet())
            .filter { it.canonicalName.simpleName == name }
    }

    /**
     * updates [allMemberFunctionOverloadSetsByName] given all the member functions of this base type.
     */
    private fun updateAllMemberFunctions(allMemberFunctions: Iterable<BoundMemberFunction>) {
        allMemberFunctionOverloadSetsByName = allMemberFunctions
            .groupBy { Pair(it.name, it.parameters.parameters.size) }
            .map { (nameAndParamCount, overloads) ->
                BoundOverloadSet(
                    CanonicalElementName.Function(
                        this@BoundBaseType.canonicalName,
                        nameAndParamCount.first,
                    ),
                    nameAndParamCount.second,
                    overloads,
                )
            }
            .groupBy { it.canonicalName.simpleName }
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableSetOf<Reporting>()

            typeParameters?.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }
            reportings.addAll(superTypes.semanticAnalysisPhase1())

            entries.forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }

            _memberVariables.duplicatesBy(BoundBaseTypeMemberVariable::name).forEach { (_, dupMembers) ->
                reportings.add(Reporting.duplicateBaseTypeMembers(this, dupMembers))
            }
            if (!kind.allowsMemberVariables) {
                _memberVariables.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
            }

            if (kind.hasCtorsAndDtors) {
                declaredConstructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> reportings.add(Reporting.multipleClassConstructors(list.map { it.declaration })) }

                declaredDestructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> reportings.add(Reporting.multipleClassDestructors(list.map { it.declaration })) }

                if (declaredConstructors.none()) {
                    val defaultCtorAst = BaseTypeConstructorDeclaration(
                        listOfNotNull(declaration.visibility),
                        KeywordToken(Keyword.CONSTRUCTOR, span = declaration.declaredAt),
                        AstCodeChunk(emptyList())
                    )
                    constructor = defaultCtorAst.bindTo(typeRootContext, typeParameters) { this }
                    reportings.addAll(constructor!!.semanticAnalysisPhase1())
                } else {
                    constructor = declaredConstructors.first()
                }
                if (declaredDestructors.none()) {
                    val defaultDtorAst = BaseTypeDestructorDeclaration(
                        KeywordToken(Keyword.DESTRUCTOR, span = declaration.declaredAt),
                        emptyList(),
                        AstCodeChunk(emptyList())
                    )
                    destructor = defaultDtorAst.bindTo(typeRootContext, typeParameters) { this }
                    reportings.addAll(destructor!!.semanticAnalysisPhase1())
                } else {
                    destructor = declaredDestructors.first()
                }
            } else {
                declaredConstructors.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
                declaredDestructors.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
            }

            if (!kind.allowMemberFunctionImplementations) {
                entries
                    .asSequence()
                    .filterIsInstance<BoundDeclaredBaseTypeMemberFunction>()
                    .filter { it.declaresReceiver }
                    .filter { it.body != null }
                    .forEach {
                        reportings.add(Reporting.memberFunctionImplementedOnInterface(it))
                    }
            }

            lintSean1(reportings)

            if (superTypes.hasCyclicInheritance) {
                return@phase1 reportings
            }

            val overriddenInheritedFunctions: MutableSet<BoundMemberFunction> = Collections.newSetFromMap(IdentityHashMap())
            val allMemberFunctions = mutableListOf<BoundMemberFunction>()
            entries.asSequence().filterIsInstance<BoundMemberFunction>().forEach {
                allMemberFunctions.add(it)
                it.overrides?.forEach(overriddenInheritedFunctions::add)
            }
            superTypes.inheritedMemberFunctions.asSequence()
                .filter { it !in overriddenInheritedFunctions }
                .forEach(allMemberFunctions::add)

            updateAllMemberFunctions(allMemberFunctions)

            allMemberFunctionOverloadSetsByName.values.forEach { overloadSets ->
                overloadSets.forEach { overloadSet ->
                    reportings.addAll(overloadSet.semanticAnalysisPhase1())
                }
            }

            return@phase1 reportings
        }
    }

    fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = _memberVariables.find { it.name == name }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            if (superTypes.hasCyclicInheritance) {
                return@phase2 emptySet()
            }

            val reportings = entries.flatMap { it.semanticAnalysisPhase2() }.toMutableList()

            typeParameters?.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }
            reportings.addAll(superTypes.semanticAnalysisPhase2())
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase2).forEach(reportings::addAll)
            constructor?.semanticAnalysisPhase2()?.let(reportings::addAll)
            destructor?.semanticAnalysisPhase2()?.let(reportings::addAll)

            allMemberFunctionOverloadSetsByName.values.forEach { overloadSets ->
                overloadSets.forEach { overloadSet ->
                    reportings.addAll(overloadSet.semanticAnalysisPhase2())
                }
            }

            return@phase2 reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3(runIfErrorsPreviously = false) {
            if (superTypes.hasCyclicInheritance) {
                return@phase3 emptySet()
            }

            val reportings = entries.flatMap { it.semanticAnalysisPhase3() }.toMutableList()

            typeParameters?.forEach { reportings.addAll(it.semanticAnalysisPhase3()) }
            reportings.addAll(superTypes.semanticAnalysisPhase3())
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase3).forEach(reportings::addAll)
            constructor?.semanticAnalysisPhase3()?.let(reportings::addAll)
            destructor?.semanticAnalysisPhase3()?.let(reportings::addAll)

            allMemberFunctionOverloadSetsByName.values.forEach { overloadSets ->
                overloadSets.forEach {
                    reportings.addAll(it.semanticAnalysisPhase3())
                }
            }

            if (!kind.memberFunctionsAbstractByDefault) {
                val overriddenSuperFns = memberFunctions
                    .asSequence()
                    .flatMap { it.overloads }
                    .flatMap { it.overrides ?: emptyList() }
                    .toCollection(Collections.newSetFromMap(IdentityHashMap()))

                val mixinImplementations = IdentityHashMap<InheritedBoundMemberFunction, BoundMixinStatement>()
                val mixins = constructor?.mixins ?: emptySet()
                for (inheritedFn in superTypes.inheritedMemberFunctions) {
                    if (!inheritedFn.isAbstract) {
                        continue
                    }
                    if (inheritedFn in overriddenSuperFns) {
                        continue
                    }

                    var originallyInheritedFrom = inheritedFn.declaredOnType
                    var pivot: InheritedBoundMemberFunction? = inheritedFn
                    while (pivot != null) {
                        originallyInheritedFrom = pivot.declaredOnType
                        pivot = pivot.supertypeMemberFn as? InheritedBoundMemberFunction
                    }

                    val responsibleMixin = mixins
                        .firstOrNull { mixin ->
                            val type = mixin.type ?: return@firstOrNull false
                            type.isAssignableTo(originallyInheritedFrom.baseReference)
                        }

                    if (responsibleMixin == null) {
                        reportings.add(Reporting.abstractInheritedFunctionNotImplemented(this, inheritedFn))
                    } else {
                        check(inheritedFn !in mixinImplementations)
                        mixinImplementations[inheritedFn] = responsibleMixin
                    }
                }
            } else {
                // if there are constructors, there could be mixins. But in this branch, they're not considered
                // if that is the case, there's a fundamental bug and the chances for miscompilation are huge
                check(!kind.hasCtorsAndDtors)
                check(constructor == null)
            }

            return@phase3 reportings
        }
    }

    override fun validateAccessFrom(location: Span): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "class $simpleName"

    private fun lintSean1(reportings: MutableCollection<Reporting>) {
        if (declaration.name.value.any { it == '_' }) {
            reportings.add(Reporting.unconventionalTypeName(declaration.name, UnconventionalTypeNameReporting.ViolatedConvention.UPPER_CAMEL_CASE))
        } else if (!declaration.name.value.first().isUpperCase()) {
            reportings.add(Reporting.unconventionalTypeName(declaration.name, UnconventionalTypeNameReporting.ViolatedConvention.FIRST_LETTER_UPPERCASE))
        }
    }

    private val _fields: MutableList<BaseTypeField> = ArrayList(memberVariables.size)
    val fields: List<BaseTypeField> = _fields

    /**
     * allocate a field of type [type] in instances of this [BoundBaseType].
     *
     * **must be called after semantic analysis is done, ideally while generating IR.**
     */
    fun allocateField(type: BoundTypeReference): BaseTypeField {
        seanHelper.requirePhase3Done()

        val field = BaseTypeField(_fields.size, type)
        _fields.add(field)

        return field
    }

    private val backendIr by lazy {
        _memberVariables.forEach {
            it.assureFieldAllocated()
        }
        kind.toBackendIr(this)
    }
    fun toBackendIr(): IrBaseType = backendIr

    override fun toString() = "${kind.name.lowercase()} $canonicalName"

    /**
     * True iff this is one of the core numeric types of the language:
     * * all the numeric types, ints and floats
     */
    val isCoreNumericType: Boolean
        get() = this in setOf(
            context.swCtx.s8,
            context.swCtx.u8,
            context.swCtx.s16,
            context.swCtx.u16,
            context.swCtx.s32,
            context.swCtx.u32,
            context.swCtx.s64,
            context.swCtx.u64,
            context.swCtx.sword,
            context.swCtx.uword,
            context.swCtx.f32,
            context.swCtx.f64,
        )

    /**
     * True iff this is one of the core scalar types of the language:
     * * all the numeric types, ints and floats
     * * bool
     */
    val isCoreScalar: Boolean
        get() = isCoreNumericType || this in setOf(
            context.swCtx.bool,
        )

    /** @return Whether this type is the same as or a subtype of the given type. */
    infix fun isSubtypeOf(other: BoundBaseType): Boolean {
        if (other === this) return true
        if (other === context.swCtx.nothing) return false
        if (this === context.swCtx.nothing) return true

        return superTypes.baseTypes
            .map { it.isSubtypeOf(other) }
            .fold(false, Boolean::or)
    }

    enum class Kind(
        val namePlural: String,
        val hasCtorsAndDtors: Boolean,
        val allowsMemberVariables: Boolean,
        val allowMemberFunctionImplementations: Boolean,
    ) {
        CLASS(
            "classes",
            hasCtorsAndDtors = true,
            allowsMemberVariables = true,
            allowMemberFunctionImplementations = true,
        ),
        INTERFACE(
            "interfaces",
            hasCtorsAndDtors = false,
            allowsMemberVariables = false,
            allowMemberFunctionImplementations = false,
        ),
        ;

        val memberFunctionsAbstractByDefault: Boolean = !allowMemberFunctionImplementations

        fun toBackendIr(typeDef: BoundBaseType): IrBaseType = when(this) {
            CLASS -> IrClassImpl(typeDef)
            INTERFACE -> IrInterfaceImpl(typeDef)
        }

        override fun toString() = name.lowercase()
    }

    companion object {
        /**
         * Suppose
         *
         *     class A
         *     class AB : A
         *     class ABC : AB
         *     class C
         *
         * then these are the closest common ancestors:
         *
         * | Types       | Closes common ancestor |
         * | ----------- | ---------------------- |
         * | A, AB       | A                      |
         * | AB, ABC     | AB                     |
         * | A, ABC      | A                      |
         * | C, A        | Any                    |
         * | AB, C       | Any                    |
         *
         * @return the most specific type that all the given types can be assigned to
         */
        fun closestCommonSupertypeOf(types: List<BoundBaseType>): BoundBaseType {
            if (types.isEmpty()) throw IllegalArgumentException("At least one type must be provided")

            val typesExcludingNothing = types.filter { it !== it.context.swCtx.nothing }
            if (typesExcludingNothing.isEmpty()) {
                return types.first() // is definitely the nothing type, just checked
            }
            if (typesExcludingNothing.size == 1) {
                return typesExcludingNothing[0]
            }

            var pivot = typesExcludingNothing[0]
            for (_type in typesExcludingNothing[1..<typesExcludingNothing.size]) {
                var type = _type
                var swapped = false
                while (!(type isSubtypeOf pivot)) {
                    if (pivot.superTypes.baseTypes.isEmpty()) return pivot.context.swCtx.any
                    if (pivot.superTypes.baseTypes.size > 1) {
                        if (swapped) {
                            return pivot.context.swCtx.any
                        }
                        val temp = pivot
                        pivot = type
                        type = temp
                        swapped = true
                    }
                    else {
                        pivot = pivot.superTypes.baseTypes.first()
                    }
                }
            }

            return pivot
        }

        /**
         * @see [closestCommonSupertypeOf]
         */
        fun closestCommonSupertypeOf(vararg types: BoundBaseType): BoundBaseType {
            return closestCommonSupertypeOf(types.asList())
        }
    }
}

private class IrInterfaceImpl(
    val typeDef: BoundBaseType,
) : IrInterface {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val supertypes: Set<IrInterface> get() = typeDef.superTypes.baseTypes.map { it.toBackendIr() as IrInterface }.toSet()
    override val parameters = typeDef.typeParameters?.map { it.toBackendIr() } ?: emptyList()
    override val memberFunctions by lazy { typeDef.memberFunctions.map { it.toBackendIr() as IrOverloadGroup<IrMemberFunction> } }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IrInterfaceImpl) return false

        if (canonicalName != other.canonicalName) return false

        return true
    }

    override fun hashCode(): Int {
        return canonicalName.hashCode()
    }
}

private class IrClassImpl(
    val typeDef: BoundBaseType,
) : IrClass {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val supertypes: Set<IrInterface> get() = typeDef.superTypes.baseTypes.map { it.toBackendIr() as IrInterface }.toSet()
    override val parameters = typeDef.typeParameters?.map { it.toBackendIr() } ?: emptyList()
    override val fields by lazy { typeDef.fields.map { it.toBackendIr() } }
    override val memberVariables by lazy { typeDef.memberVariables.map { it.toBackendIr() } }
    override val memberFunctions by lazy { typeDef.memberFunctions.map { it.toBackendIr() as IrOverloadGroup<IrMemberFunction> } }
    override val constructor by lazy { typeDef.constructor!!.toBackendIr() }
    override val destructor by lazy { typeDef.destructor!!.toBackendIr() }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IrClassImpl) return false

        if (canonicalName != other.canonicalName) return false

        return true
    }

    override fun hashCode(): Int {
        return canonicalName.hashCode()
    }
}