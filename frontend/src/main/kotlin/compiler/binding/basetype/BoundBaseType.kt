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

import compiler.ast.AstCodeChunk
import compiler.ast.BaseTypeDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.AstWildcardTypeArgument
import compiler.ast.type.TypeVariance
import compiler.binding.AccessorKind
import compiler.binding.BoundElement
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.binding.SeanHelper
import compiler.binding.basetype.BoundBaseType.Companion.closestCommonSupertypeOf
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.IrSimpleTypeImpl
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.isAssignableTo
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.UnconventionalTypeNameDiagnostic
import compiler.diagnostic.duplicateBaseTypeMembers
import compiler.diagnostic.entryNotAllowedOnBaseType
import compiler.diagnostic.getterAndSetterWithDifferentType
import compiler.diagnostic.memberFunctionImplementedOnInterface
import compiler.diagnostic.multipleAccessorsOnBaseType
import compiler.diagnostic.unconventionalTypeName
import compiler.diagnostic.unsupportedVarianceOnBaseTypeTypeParameter
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
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.common.CanonicalElementName
import kotlinext.duplicatesBy
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
    private val bindTimeDiagnosis: CollectingDiagnosis,
) : BoundElement<BaseTypeDeclaration>, DefinitionWithVisibility {
    private val seanHelper = SeanHelper()

    override val context: CTContext = fileContext
    val canonicalName: CanonicalElementName.BaseType by lazy {
        CanonicalElementName.BaseType(context.packageName, declaration.name.value)
    }
    val simpleName: String = declaration.name.value

    private lateinit var entries: List<BoundBaseTypeEntry<*>>
    lateinit var memberVariables: List<BoundBaseTypeMemberVariable>
        private set
    lateinit var declaredConstructors: Sequence<BoundClassConstructor>
        private set
    lateinit var declaredDestructors: Sequence<BoundClassDestructor>
        private set
    var constructor: BoundClassConstructor? = null
        private set

    /**
     * Late initialization so that references to this base-type can already be created in the entries
     * (member variables and constructor code).
     */
    fun init(constructor: BoundClassConstructor, memberVariables: List<BoundBaseTypeMemberVariable>, nonVariableEntries: List<BoundBaseTypeEntry<*>>) {
        this.constructor = constructor.takeIf { kind.hasCtorsAndDtors }
        this.memberVariables = memberVariables
        declaredDestructors = nonVariableEntries.filterIsInstance<BoundClassDestructor>().asSequence()

        this.entries = listOf(constructor) + memberVariables + nonVariableEntries
    }

    private fun buildBoundReference(arguments: List<BoundTypeArgument>?, span: Span): RootResolvedTypeReference {
        return RootResolvedTypeReference(
            this.context,
            AstAbsoluteTypeReference(canonicalName, span = span.deriveGenerated()),
            this,
            arguments,
        )
    }

    private val cachedReferenceNoneOrWildcardTypeArgumentsUnknownSpan by lazy {
        buildBoundReference(
            typeParameters?.map { typeParam ->
                context.resolveTypeArgument(AstWildcardTypeArgument.INSTANCE, typeParam)
            },
            Span.UNKNOWN
        )
    }

    fun getBoundReferenceAssertNoTypeParameters(span: Span = Span.UNKNOWN): RootResolvedTypeReference {
        require(typeParameters.isNullOrEmpty())

        return if (span == Span.UNKNOWN) cachedReferenceNoneOrWildcardTypeArgumentsUnknownSpan else buildBoundReference(null, span)
    }

    fun getBoundReferenceWithNoneOrWildcardTypeArguments(span: Span = Span.UNKNOWN): RootResolvedTypeReference {
        return if (span == Span.UNKNOWN) {
            cachedReferenceNoneOrWildcardTypeArgumentsUnknownSpan
        } else {
            buildBoundReference(
                cachedReferenceNoneOrWildcardTypeArgumentsUnknownSpan.arguments,
                span,
            )
        }
    }

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    var destructor: BoundClassDestructor? by seanHelper.resultOfPhase1()
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
            bindTimeDiagnosis.replayOnto(diagnosis)

            typeParameters?.forEach {
                it.semanticAnalysisPhase1(diagnosis)
                if (it.astNode.variance != TypeVariance.UNSPECIFIED) {
                    diagnosis.unsupportedVarianceOnBaseTypeTypeParameter(it)
                }
            }
            superTypes.semanticAnalysisPhase1(diagnosis)

            entries.forEach {
                it.semanticAnalysisPhase1(diagnosis)
            }

            if (kind.hasCtorsAndDtors) {
                if (declaredDestructors.none()) {
                    val defaultDtorAst = BaseTypeDestructorDeclaration(
                        KeywordToken(Keyword.DESTRUCTOR, span = declaration.declaredAt),
                        emptyList(),
                        AstCodeChunk(emptyList())
                    )
                    destructor = defaultDtorAst.bindTo(context, typeRootContext, typeParameters) { this }
                    destructor!!.semanticAnalysisPhase1(diagnosis)
                } else {
                    destructor = declaredDestructors.first()
                }
            } else {
                destructor = null
            }

            memberVariables.duplicatesBy(BoundBaseTypeMemberVariable::name).forEach { (_, dupMembers) ->
                diagnosis.duplicateBaseTypeMembers(this, dupMembers)
            }
            if (!kind.allowsMemberVariables) {
                memberVariables.forEach {
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
                        memberVar!!.entryDeclaration,
                        accessorFns,
                    )
                }
        }
    }

    fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = memberVariables.find { it.name == name }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            entries.forEach { it.semanticAnalysisPhase2(diagnosis) }

            typeParameters?.forEach { it.semanticAnalysisPhase2(diagnosis) }
            superTypes.semanticAnalysisPhase2(diagnosis)
            entries.forEach { it.semanticAnalysisPhase2(diagnosis) }
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
                            type.isAssignableTo(originallyInheritedFrom.getBoundReferenceWithNoneOrWildcardTypeArguments())
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

    private val _fields: MutableList<BaseTypeField> = ArrayList()
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
        memberVariables.forEach {
            it.assureFieldAllocated()
        }
        kind.toBackendIr(this)
    }
    fun toBackendIr(): IrBaseType = backendIr

    val irReadNotNullReference: IrType by lazy {
        IrSimpleTypeImpl(backendIr, IrTypeMutability.READONLY, false)
    }

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
    infix fun isSubtypeOf(supertype: BoundBaseType): Boolean {
        if (supertype === this) return true
        if (supertype === context.swCtx.any) return true
        if (supertype === context.swCtx.nothing) return false
        if (this === context.swCtx.nothing) return true

        return supertype in this.superTypes.preprocessedInheritanceTree.parameterizedSupertypes.keys
    }

    enum class Kind(
        val namePlural: String,
        val hasCtorsAndDtors: Boolean,
        val allowsMemberVariables: Boolean,
        val allowMemberFunctionImplementations: Boolean,
        val allowsSubtypes: Boolean,
    ) {
        CLASS(
            "classes",
            hasCtorsAndDtors = true,
            allowsMemberVariables = true,
            allowMemberFunctionImplementations = true,
            allowsSubtypes = false,
        ),
        INTERFACE(
            "interfaces",
            hasCtorsAndDtors = false,
            allowsMemberVariables = false,
            allowMemberFunctionImplementations = false,
            allowsSubtypes = true,
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

            var pivot = typesExcludingNothing.first()
            for (_type in typesExcludingNothing.drop(1)) {
                var type = _type
                var swapped = false
                while (!(type isSubtypeOf pivot)) {
                    if (pivot.superTypes.directSuperBaseTypes.isEmpty()) return pivot.context.swCtx.any
                    if (pivot.superTypes.directSuperBaseTypes.size > 1) {
                        if (swapped) {
                            return pivot.context.swCtx.any
                        }
                        val temp = pivot
                        pivot = type
                        type = temp
                        swapped = true
                    }
                    else {
                        pivot = pivot.superTypes.directSuperBaseTypes.first()
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
    override val supertypes: Set<IrInterface> get() = typeDef.superTypes.directSuperBaseTypes.map { it.toBackendIr() as IrInterface }.toSet()
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

    override fun toString() = "IrInterface[$canonicalName]"
}

private class IrClassImpl(
    val typeDef: BoundBaseType,
) : IrClass {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val supertypes: Set<IrInterface> get() = typeDef.superTypes.directSuperBaseTypes.map { it.toBackendIr() as IrInterface }.toSet()
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