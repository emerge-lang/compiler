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

package compiler.binding.classdef

import compiler.OnceAction
import compiler.ast.ClassDeclaration
import compiler.ast.FunctionDeclaration
import compiler.binding.BoundElement
import compiler.binding.BoundFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.context.CTContext
import compiler.binding.misc_ir.IrOverloadGroupImpl
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BuiltinAny
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import kotlinext.duplicatesBy

class BoundClassDefinition(
    fileContext: CTContext,
    val classRootContext: CTContext,
    override val typeParameters: List<BoundTypeParameter>,
    override val declaration: ClassDeclaration,
    val members: List<BoundClassMemberVariable>, // TODO: widen to BoundClassMember once functions are supported
) : BaseType, BoundElement<ClassDeclaration> {
    private val onceAction = OnceAction()

    override val context: CTContext = fileContext
    override val fullyQualifiedName get() = context.sourceFile.packageName + declaration.name.value
    override val simpleName: String = declaration.name.value

    override val superTypes: Set<BaseType> = setOf(BuiltinAny)

    // this can only be initialized in semanticAnalysisPhase1 because the types referenced in the members
    // can be declared later than the class
    override lateinit var constructors: Collection<BoundOverloadSet>
        private set

    override fun resolveMemberFunction(name: String): Collection<FunctionDeclaration> = emptySet()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            typeParameters.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }

            members.forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }

            members.duplicatesBy(BoundClassMemberVariable::name).forEach { (_, dupMembers) ->
                reportings.add(Reporting.duplicateTypeMembers(this, dupMembers))
            }

            constructors = setOf(BoundOverloadSet.fromSingle(ClassConstructor(this)))
            constructors.flatMap { it.overloads }.map { it.semanticAnalysisPhase1() }.forEach(reportings::addAll)
            constructors.map { it.semanticAnalysisPhase1() }.forEach(reportings::addAll)

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = members.flatMap { it.semanticAnalysisPhase2() }.toMutableList()
            constructors.flatMap { it.overloads }.map(BoundFunction::semanticAnalysisPhase2).forEach(reportings::addAll)
            constructors.map { it.semanticAnalysisPhase2() }.forEach(reportings::addAll)
            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase2).forEach(reportings::addAll)
            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = members.flatMap { it.semanticAnalysisPhase3() }.toMutableList()
            constructors.flatMap { it.overloads }.map(BoundFunction::semanticAnalysisPhase3).forEach(reportings::addAll)
            constructors.map { it.semanticAnalysisPhase3() }.forEach(reportings::addAll)
            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)
            return@getResult reportings
        }
    }

    override fun resolveMemberVariable(name: String): BoundClassMember? = members.find { it.name == name }

    private val backendIr by lazy { IrClassImpl(this) }
    override fun toBackendIr(): IrClass = backendIr
}

private class IrClassImpl(
    classDef: BoundClassDefinition,
) : IrClass {
    override val fqn: DotName = classDef.fullyQualifiedName
    override val parameters = classDef.typeParameters.map { it.toBackendIr() }
    override val members = classDef.members.map { it.toBackendIr() }
    override val constructors = classDef.constructors.map {
        IrOverloadGroupImpl(it.fqn, it.parameterCount, it.overloads)
    }.toSet()
}