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

import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.CodeChunk
import compiler.binding.BoundElement
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVisibility
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.handleCyclicInvocation
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.reportings.CyclicInheritanceReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import kotlinext.duplicatesBy
import java.util.Collections
import java.util.IdentityHashMap

class BoundBaseTypeDefinition(
    private val fileContext: CTContext,
    private val typeRootContext: CTContext,
    val kind: Kind,
    override val visibility: BoundVisibility,
    override val typeParameters: List<BoundTypeParameter>,
    override val superTypes: BoundSupertypeList,
    override val declaration: BaseTypeDeclaration,
    val entries: List<BoundBaseTypeEntry<*>>,
) : BaseType, BoundElement<BaseTypeDeclaration> {
    private val seanHelper = SeanHelper()

    override val context: CTContext = fileContext
    override val canonicalName by lazy {
        CanonicalElementName.BaseType(context.sourceFile.packageName, declaration.name.value)
    }
    override val simpleName: String = declaration.name.value

    val memberVariables: List<BoundBaseTypeMemberVariable> = entries.filterIsInstance<BoundBaseTypeMemberVariable>()
    val declaredConstructors: Sequence<BoundClassConstructor> = entries.asSequence().filterIsInstance<BoundClassConstructor>()
    val declaredDestructors: Sequence<BoundClassDestructor> = entries.asSequence().filterIsInstance<BoundClassDestructor>()

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    override var constructor: BoundClassConstructor? = null
        private set

    /**
     * Always `null` if [Kind.hasCtorsAndDtors] is `false`. If `true`, is initialized in
     * [semanticAnalysisPhase1] to a given declaration or a generated one.
     */
    override var destructor: BoundClassDestructor? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableSetOf<Reporting>()

            typeParameters.flatMap { it.semanticAnalysisPhase1() }.forEach(reportings::add)
            reportings.addAll(superTypes.semanticAnalysisPhase1())

            entries.forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }

            memberVariables.duplicatesBy(BoundBaseTypeMemberVariable::name).forEach { (_, dupMembers) ->
                reportings.add(Reporting.duplicateBaseTypeMembers(this, dupMembers))
            }
            if (!kind.allowsMemberVariables) {
                memberVariables.forEach {
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
                    val defaultCtorAst = BaseTypeConstructorDeclaration(emptyList(), IdentifierToken("constructor", declaration.declaredAt), CodeChunk(emptyList()))
                    // TODO: maybe has to be bound to fileContextWithTypeParameters
                    constructor = defaultCtorAst.bindTo(typeRootContext, typeParameters) { this }
                    reportings.addAll(constructor!!.semanticAnalysisPhase1())
                } else {
                    constructor = declaredConstructors.first()
                }
                if (declaredDestructors.none()) {
                    val defaultDtorAst = BaseTypeDestructorDeclaration(IdentifierToken("destructor", declaration.declaredAt), CodeChunk(emptyList()))
                    // TODO: maybe has to be bound to fileContextWithTypeParameters
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

            return@phase1 reportings
        }
    }

    private var cyclicInheritanceTested = false
    private var cyclicInheritanceDetected = false
    /**
     * does _nothing_ except invoking this method on all the supertypes of this type,
     * and by that in turn on all supertypes in the hierarchy. If there is a cycle in the subtype<->supertype
     * graph, this will enter an endless loop/stack overflow. That is detected using [handleCyclicInvocation]
     * to produce a reporting on an illegal inheritance cycle.
     *
     * To be invoked during [semanticAnalysisPhase2]
     */
    internal fun walkAllSupertypes(): Collection<CyclicInheritanceReporting> {
        if (cyclicInheritanceTested) {
            return emptySet()
        }

        val cyclicReportings = superTypes.clauses
            // TODO: remove this filter as soon as all basetypes are declared in emerge source - it shouldn't be necessary then
            .filterIsInstance<SourceBoundSupertypeDeclaration>()
            .filter { it.resolvedReference != null }
            .filter { it.resolvedReference!!.baseType is BoundBaseTypeDefinition }  // TODO: this should go away with the filterIsInstance above
            .flatMap { supertypeDecl ->
                val superBasetype = supertypeDecl.resolvedReference!!.baseType
                superBasetype as BoundBaseTypeDefinition
                handleCyclicInvocation(
                    this,
                    action = {
                        superBasetype.walkAllSupertypes()
                    },
                    onCycle = {
                        setOf(Reporting.cyclicInheritance(this, supertypeDecl))
                    }
                )
            }

        cyclicInheritanceTested = true
        cyclicInheritanceDetected = cyclicReportings.isNotEmpty()
        return cyclicReportings
    }


    private lateinit var allMemberFunctionOverloadSetsByName: Map<String, Collection<BoundOverloadSet<BoundMemberFunction>>>

    override fun resolveMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        semanticAnalysisPhase2()
        if (!this::allMemberFunctionOverloadSetsByName.isInitialized) {
            return emptySet()
        }

        return allMemberFunctionOverloadSetsByName.getOrDefault(name, emptySet())
            .filter { it.canonicalName.simpleName == name }
    }

    override val memberFunctions: Collection<BoundOverloadSet<BoundMemberFunction>>
        get() {
            seanHelper.requirePhase2Done()
            if (!this::allMemberFunctionOverloadSetsByName.isInitialized) {
                return emptySet()
            }

            return allMemberFunctionOverloadSetsByName.values.flatten()
        }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val cyclicInheritanceErrors = walkAllSupertypes()
            if (cyclicInheritanceErrors.isNotEmpty()) {
                return@phase2 cyclicInheritanceErrors
            }
            if (cyclicInheritanceDetected) {
                return@phase2 setOf(Reporting.consecutive("not validating further due to cyclic inheritance", declaration.declaredAt))
            }

            val reportings = entries.flatMap { it.semanticAnalysisPhase2() }.toMutableList()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase2).forEach(reportings::addAll)
            reportings.addAll(superTypes.semanticAnalysisPhase2())
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase2).forEach(reportings::addAll)
            constructor?.semanticAnalysisPhase2()?.let(reportings::addAll)
            destructor?.semanticAnalysisPhase2()?.let(reportings::addAll)

            val overriddenInheritedFunctions: MutableSet<BoundMemberFunction> = Collections.newSetFromMap(IdentityHashMap())
            val allMemberFunctions = mutableListOf<BoundMemberFunction>()
            entries.asSequence().filterIsInstance<BoundMemberFunction>().forEach {
                allMemberFunctions.add(it)
                it.overrides?.forEach(overriddenInheritedFunctions::add)
            }
            superTypes.inheritedMemberFunctions.asSequence()
                .filter { it !in overriddenInheritedFunctions }
                .forEach(allMemberFunctions::add)

            allMemberFunctionOverloadSetsByName = allMemberFunctions
                .groupBy { Pair(it.name, it.parameters.parameters.size) }
                .map { (nameAndParamCount, overloads) ->
                    BoundOverloadSet(
                        CanonicalElementName.Function(
                            this@BoundBaseTypeDefinition.canonicalName,
                            nameAndParamCount.first,
                        ),
                        nameAndParamCount.second,
                        overloads,
                    )
                }
                .groupBy { it.canonicalName.simpleName }

            allMemberFunctionOverloadSetsByName.values.forEach { overloadSets ->
                overloadSets.forEach { overloadSet ->
                    reportings.addAll(overloadSet.semanticAnalysisPhase1())
                    reportings.addAll(overloadSet.semanticAnalysisPhase2())
                }
            }

            // TODO?: merge inherited and declared member fns
            // TODO?: on all inherited member functions, narrow the type of the receiver to the subtype


            return@phase2 reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3(runIfErrorsPreviously = false) {
            val reportings = entries.flatMap { it.semanticAnalysisPhase3() }.toMutableList()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)
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

                superTypes.inheritedMemberFunctions
                    .filter { it.isAbstract }
                    .forEach { abstractSuperFn ->
                        if (abstractSuperFn !in overriddenSuperFns) {
                            reportings.add(Reporting.abstractInheritedFunctionNotImplemented(this, abstractSuperFn))
                        }
                    }
            }

            return@phase3 reportings
        }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "class $simpleName"

    override fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = memberVariables.find { it.name == name }

    private val backendIr by lazy { kind.toBackendIr(this) }
    override fun toBackendIr(): IrBaseType = backendIr

    override fun toString() = "${kind.name.lowercase()} $canonicalName"

    enum class Kind(
        val namePlural: String,
        val hasCtorsAndDtors: Boolean,
        val allowsMemberVariables: Boolean,
        val memberFunctionsAbstractByDefault: Boolean,
        val memberFunctionsVirtualByDefault: Boolean,
    ) {
        CLASS("classes", hasCtorsAndDtors = true, allowsMemberVariables = true, memberFunctionsAbstractByDefault = false, memberFunctionsVirtualByDefault = false),
        INTERFACE("interfaces", hasCtorsAndDtors = false, allowsMemberVariables = false, memberFunctionsAbstractByDefault = true, memberFunctionsVirtualByDefault = true),
        ;

        fun toBackendIr(typeDef: BoundBaseTypeDefinition): IrBaseType = when(this) {
            CLASS -> IrClassImpl(typeDef)
            INTERFACE -> IrInterfaceImpl(typeDef)
        }
    }
}

private class IrInterfaceImpl(
    typeDef: BoundBaseTypeDefinition,
) : IrInterface {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val parameters = typeDef.typeParameters.map { it.toBackendIr() }
    override val memberFunctions by lazy { typeDef.memberFunctions.map { it.toBackendIr() as IrOverloadGroup<IrMemberFunction> } }
}

private class IrClassImpl(
    typeDef: BoundBaseTypeDefinition,
) : IrClass {
    override val canonicalName: CanonicalElementName.BaseType = typeDef.canonicalName
    override val parameters = typeDef.typeParameters.map { it.toBackendIr() }
    override val memberVariables by lazy { typeDef.memberVariables.map { it.toBackendIr() } }
    override val memberFunctions by lazy { typeDef.memberFunctions.map { it.toBackendIr() as IrOverloadGroup<IrMemberFunction> } }
    override val constructor by lazy { typeDef.constructor!!.toBackendIr() }
    override val destructor by lazy { typeDef.destructor!!.toBackendIr() }
}