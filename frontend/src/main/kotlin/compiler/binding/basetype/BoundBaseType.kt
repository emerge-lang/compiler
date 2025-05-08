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
import compiler.ast.type.NamedTypeReference
import compiler.binding.AccessorKind
import compiler.binding.BoundElement
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.isAssignableTo
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.UnconventionalTypeNameDiagnostic
import compiler.diagnostic.duplicateBaseTypeMembers
import compiler.diagnostic.entryNotAllowedOnBaseType
import compiler.diagnostic.getterAndSetterWithDifferentType
import compiler.diagnostic.memberFunctionImplementedOnInterface
import compiler.diagnostic.multipleAccessorsOnBaseType
import compiler.diagnostic.multipleClassConstructors
import compiler.diagnostic.multipleClassDestructors
import compiler.diagnostic.unconventionalTypeName
import compiler.diagnostic.unusedMixin
import compiler.diagnostic.virtualAndActualMemberVariableNameClash
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import io.github.tmarsteel.emerge.common.CanonicalElementName
import kotlinext.duplicatesBy
import kotlinext.get
import java.util.Collections
import java.util.IdentityHashMap

class BoundBaseType(
    private val fileContext: CTContext,
    val typeRootContext: CTContext,
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
    val baseReference: RootResolvedTypeReference get() {
        return RootResolvedTypeReference(
            context,
            NamedTypeReference(this.simpleName),
            this,
            if (typeParameters.isNullOrEmpty()) null else throw InternalCompilerError("cannot use baseReference on types with parameters")
        )
    }

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
        seanHelper.requirePhase1Done()
        if (!this::allMemberFunctionOverloadSetsByName.isInitialized) {
            return emptySet()
        }

        return allMemberFunctionOverloadSetsByName.getOrDefault(name, emptySet())
            .filter { it.canonicalName.simpleName == name }
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {

            typeParameters?.forEach { it.semanticAnalysisPhase1(diagnosis) }
            superTypes.semanticAnalysisPhase1(diagnosis)

            entries.forEach {
                it.semanticAnalysisPhase1(diagnosis)
            }

            _memberVariables.duplicatesBy(BoundBaseTypeMemberVariable::name).forEach { (_, dupMembers) ->
                diagnosis.duplicateBaseTypeMembers(this, dupMembers)
            }
            if (!kind.allowsMemberVariables) {
                _memberVariables.forEach {
                    diagnosis.entryNotAllowedOnBaseType(this, it)
                }
            }

            if (kind.hasCtorsAndDtors) {
                declaredConstructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> diagnosis.multipleClassConstructors(list.map { it.declaration }) }

                declaredDestructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> diagnosis.multipleClassDestructors(list.map { it.declaration }) }

                if (declaredConstructors.none()) {
                    val defaultCtorAst = BaseTypeConstructorDeclaration(
                        listOfNotNull(declaration.visibility),
                        KeywordToken(Keyword.CONSTRUCTOR, span = declaration.declaredAt),
                        AstCodeChunk(emptyList())
                    )
                    constructor = defaultCtorAst.bindTo(typeRootContext, typeParameters) { this }
                    constructor!!.semanticAnalysisPhase1(diagnosis)
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
                    destructor!!.semanticAnalysisPhase1(diagnosis)
                } else {
                    destructor = declaredDestructors.first()
                }
            } else {
                declaredConstructors.forEach {
                    diagnosis.entryNotAllowedOnBaseType(this, it)
                }
                declaredDestructors.forEach {
                    diagnosis.entryNotAllowedOnBaseType(this, it)
                }
            }

            if (!kind.allowMemberFunctionImplementations) {
                entries
                    .asSequence()
                    .filterIsInstance<BoundDeclaredBaseTypeMemberFunction>()
                    .filter { it.declaresReceiver }
                    .filter { it.body != null }
                    .forEach {
                        diagnosis.memberFunctionImplementedOnInterface(it)
                    }
            }

            lintSean1(diagnosis)

            if (superTypes.hasCyclicInheritance) {
                return@phase1
            }

            val overriddenInheritedFunctions: MutableSet<BoundMemberFunction> = Collections.newSetFromMap(IdentityHashMap())
            val allMemberFunctions = mutableListOf<BoundMemberFunction>()
            entries.asSequence().filterIsInstance<BoundMemberFunction>().forEach {
                allMemberFunctions.add(it)
                it.overrides?.forEach(overriddenInheritedFunctions::add)
            }
            superTypes.inheritedMemberFunctions.asSequence()
                .filter { it !in overriddenInheritedFunctions }
                .map {
                    if (kind.memberFunctionsAbstractByDefault) it else PossiblyMixedInBoundMemberFunction(this, it)
                }
                .forEach(allMemberFunctions::add)

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

            allMemberFunctionOverloadSetsByName.values.forEach { overloadSets ->
                overloadSets.forEach { overloadSet ->
                    overloadSet.semanticAnalysisPhase1(diagnosis)
                }
            }

            allMemberFunctions
                .asSequence()
                .filter { it.attributes.firstAccessorAttribute != null }
                .groupBy { it.name }
                .entries
                .map { (name, accessorFns) -> Pair(accessorFns, memberVariables.find { it.name == name }) }
                .filter { (_, memberVar) -> memberVar != null }
                .forEach { (accessorFns, memberVar) ->
                    diagnosis.virtualAndActualMemberVariableNameClash(
                        memberVar!!.declaration,
                        accessorFns,
                    )
                }
        }
    }

    fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = _memberVariables.find { it.name == name }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            if (superTypes.hasCyclicInheritance) {
                return@phase2
            }

            entries.forEach { it.semanticAnalysisPhase2(diagnosis) }

            typeParameters?.forEach { it.semanticAnalysisPhase2(diagnosis) }
            superTypes.semanticAnalysisPhase2(diagnosis)
            entries.forEach { it.semanticAnalysisPhase2(diagnosis) }
            constructor?.semanticAnalysisPhase2(diagnosis)
            destructor?.semanticAnalysisPhase2(diagnosis)

            allMemberFunctionOverloadSetsByName.values.forEach { overloadSets ->
                overloadSets.forEach { overloadSet ->
                    overloadSet.semanticAnalysisPhase2(diagnosis)
                }
            }

            allMemberFunctionOverloadSetsByName.forEach { memberFnName, overloadSets ->
                val byKind = overloadSets.asSequence()
                    .flatMap { it.overloads }
                    .filter { it.attributes.firstAccessorAttribute != null }
                    .groupBy { it.attributes.firstAccessorAttribute!!.kind }

                byKind
                    .filter { (kind, _ ) ->
                        // getters need not be checked: by necessity of their contract, they will form an overload set,
                        // and if there is more than one fn in that set, it is an ambiguity that is reported elsewhere
                        kind in setOf(AccessorKind.Write)
                    }
                    .filter { (_, accessors) -> accessors.size > 1 }
                    .forEach { (kind, accessors) ->
                        diagnosis.multipleAccessorsOnBaseType(memberFnName, kind, accessors)
                    }

                val getter = byKind[AccessorKind.Read]?.firstOrNull()
                val getterType = getter?.let(AccessorKind.Read::extractMemberType)
                val setter = byKind[AccessorKind.Write]?.firstOrNull()
                val setterType = setter?.let(AccessorKind.Write::extractMemberType)
                if (getterType != null && setterType != null && getterType != setterType) {
                    diagnosis.getterAndSetterWithDifferentType(memberFnName, getter, setter)
                }
            }
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis, runIfErrorsPreviously = false) {
            if (superTypes.hasCyclicInheritance) {
                return@phase3
            }

            if (!kind.memberFunctionsAbstractByDefault) {
                val memberFunctionsNeedingMixin = allMemberFunctionOverloadSetsByName.values
                    .flatten()
                    .flatMap { it.overloads }
                    .filterIsInstance<PossiblyMixedInBoundMemberFunction>()

                val mixins = constructor?.mixins ?: emptySet()
                for (fnNeedingMixin in memberFunctionsNeedingMixin) {
                    var originallyInheritedFrom = fnNeedingMixin.declaredOnType
                    var pivot: InheritedBoundMemberFunction? = fnNeedingMixin.inheritedFn
                    while (pivot != null) {
                        originallyInheritedFrom = pivot.declaredOnType
                        pivot = pivot.supertypeMemberFn as? InheritedBoundMemberFunction
                    }

                    mixins
                        .firstOrNull { mixin ->
                            val type = mixin.type ?: return@firstOrNull false
                            type.isAssignableTo(originallyInheritedFrom.baseReference)
                        }
                        ?.assignToFunction(fnNeedingMixin)
                }
            } else {
                // if there are constructors, there could be mixins. But in this branch, they're not considered
                // if that is the case, there's a fundamental bug and the chances for miscompilation are huge
                check(!kind.hasCtorsAndDtors)
                check(constructor == null)
            }
            typeParameters?.forEach { it.semanticAnalysisPhase3(diagnosis) }
            superTypes.semanticAnalysisPhase3(diagnosis)
            entries.forEach { it.semanticAnalysisPhase3(diagnosis) }
            constructor?.semanticAnalysisPhase3(diagnosis)
            destructor?.semanticAnalysisPhase3(diagnosis)

            allMemberFunctionOverloadSetsByName.values
                .flatten()
                .flatMap { it.overloads }
                .forEach { it.semanticAnalysisPhase3(diagnosis) }

            constructor?.mixins
                ?.filter { !it.used }
                ?.forEach(diagnosis::unusedMixin)
        }
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        visibility.validateAccessFrom(location, this, diagnosis)
    }

    override fun toStringForErrorMessage() = "class $simpleName"

    private fun lintSean1(diagnosis: Diagnosis) {
        if (declaration.name.value.any { it == '_' }) {
            diagnosis.unconventionalTypeName(declaration.name, UnconventionalTypeNameDiagnostic.ViolatedConvention.UPPER_CAMEL_CASE)
        } else if (!declaration.name.value.first().isUpperCase()) {
            diagnosis.unconventionalTypeName(declaration.name, UnconventionalTypeNameDiagnostic.ViolatedConvention.FIRST_LETTER_UPPERCASE)
        }
    }

    private val _fields: MutableList<BaseTypeField> = ArrayList(memberVariables.size)
    val fields: List<BaseTypeField> = _fields

    /**
     * allocate a field of type [type] in instances of this [BoundBaseType].
     *
     * **must be called before semantic analysis is done, latest before generating IR.**
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