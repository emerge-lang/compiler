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

import compiler.OnceAction
import compiler.ast.BaseTypeDeclaration
import compiler.binding.BoundElement
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVisibility
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BuiltinAny
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import kotlinext.duplicatesBy

class BoundBaseTypeDefinition(
    fileContext: CTContext,
    private val typeRootContext: CTContext,
    val kind: Kind,
    override val visibility: BoundVisibility,
    override val typeParameters: List<BoundTypeParameter>,
    override val declaration: BaseTypeDeclaration,
    val entries: List<BoundBaseTypeEntry<*>>,
) : BaseType, BoundElement<BaseTypeDeclaration> {
    private val onceAction = OnceAction()

    override val context: CTContext = fileContext
    override val fullyQualifiedName get() = context.sourceFile.packageName + declaration.name.value
    override val simpleName: String = declaration.name.value

    override val superTypes: Set<BaseType> = setOf(BuiltinAny)

    val memberVariables: List<BoundBaseTypeMemberVariable> = entries.filterIsInstance<BoundBaseTypeMemberVariable>()
    val constructors: Sequence<BoundClassConstructor> = entries.asSequence().filterIsInstance<BoundClassConstructor>()
    val destructors: Sequence<BoundClassDestructor> = entries.asSequence().filterIsInstance<BoundClassDestructor>()

    val memberFunctionsByName: Map<String, Collection<BoundOverloadSet>> by lazy {
        entries.filterIsInstance<BoundBaseTypeMemberFunction>()
            .groupBy { it.name }
            .mapValues { (name, overloadsSameName) ->
                // this is currently needed because: class member function is really just a spin on the top level
                // function, so there is a clash in the FQN logic. Also, FQNs are not really used now, this conflict
                // probably needn't be resolved if we ditch FQNs altogether
                val overloadSetFqn = this@BoundBaseTypeDefinition.context.sourceFile.packageName + name
                overloadsSameName
                    .groupBy { it.functionInstance.parameters.parameters.size }
                    .map { (parameterCount, overloads) ->

                        BoundOverloadSet(overloadSetFqn, parameterCount, overloads.map { it.functionInstance })
                    }
            }
    }

    // this can only be initialized in semanticAnalysisPhase1 because the types referenced in the members
    // can be declared later than the class
    override val constructor = constructors.first()
    override val destructor = destructors.first()

    override fun resolveMemberFunction(name: String): Collection<BoundOverloadSet> = memberFunctionsByName[name] ?: emptySet()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            typeParameters.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }

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

            if (kind.allowsCtorsAndDtors) {
                constructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> reportings.add(Reporting.multipleClassConstructors(list.map { it.declaration })) }

                destructors
                    .drop(1)
                    .toList()
                    .takeUnless { it.isEmpty() }
                    ?.let { list -> reportings.add(Reporting.multipleClassDestructors(list.map { it.declaration })) }
            } else {
                constructors.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
                destructors.forEach {
                    reportings.add(Reporting.entryNotAllowedOnBaseType(this, it))
                }
            }

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = entries.flatMap { it.semanticAnalysisPhase2() }.toMutableList()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase2).forEach(reportings::addAll)
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase2).forEach(reportings::addAll)

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = entries.flatMap { it.semanticAnalysisPhase3() }.toMutableList()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)
            entries.map(BoundBaseTypeEntry<*>::semanticAnalysisPhase3).forEach(reportings::addAll)

            return@getResult reportings
        }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "class $simpleName"

    override fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = memberVariables.find { it.name == name }

    private val backendIr by lazy { IrClassImpl(this) }
    override fun toBackendIr(): IrClass = backendIr

    enum class Kind(
        val namePlural: String,
        val allowsCtorsAndDtors: Boolean,
        val allowsMemberVariables: Boolean,
    ) {
        CLASS("classes", allowsCtorsAndDtors = true, allowsMemberVariables = true),
        INTERFACE("interfaces", allowsCtorsAndDtors = false, allowsMemberVariables = false),
        ;
    }
}

private class IrClassImpl(
    classDef: BoundBaseTypeDefinition,
) : IrClass {
    override val fqn: DotName = classDef.fullyQualifiedName
    override val parameters = classDef.typeParameters.map { it.toBackendIr() }
    override val memberVariables = classDef.memberVariables.map { it.toBackendIr() }
    override val memberFunctions = classDef.memberFunctionsByName.values.flatten().map { it.toBackendIr() }
    override val constructor by lazy { classDef.constructor.toBackendIr() }
    override val destructor by lazy { classDef.destructor.toBackendIr() }
}