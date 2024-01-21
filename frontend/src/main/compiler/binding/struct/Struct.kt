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

package compiler.binding.struct

import compiler.OnceAction
import compiler.ast.Executable
import compiler.ast.FunctionDeclaration
import compiler.ast.struct.StructDeclaration
import compiler.binding.BoundElement
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.binding.type.BuiltinAny
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeParameter
import compiler.reportings.Reporting
import kotlinext.duplicatesBy

class Struct(
    private val structContext: StructContext,
    override val declaration: StructDeclaration,
    val members: List<StructMember>
) : BaseType, BoundElement<StructDeclaration> {
    private val onceAction = OnceAction()

    override val context: CTContext = structContext
    override val simpleName: String = declaration.name.value
    override val typeParameters: List<BoundTypeParameter> = structContext.typeParameters
    override val superTypes: Set<BaseType> = setOf(BuiltinAny)

    // this can only be initialized in semanticAnalysisPhase1 because the types referenced in the members
    // can be declared later than the struct
    override lateinit var constructors: Set<BoundFunction>
        private set

    override fun resolveMemberFunction(name: String): Collection<FunctionDeclaration> = emptySet()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            typeParameters.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }

            members.forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }

            // duplicate members
            members.duplicatesBy(StructMember::name).forEach { (_, dupMembers) ->
                reportings.add(Reporting.duplicateTypeMembers(this, dupMembers))
            }

            constructors = setOf(StructConstructor(this))

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = members.flatMap { it.semanticAnalysisPhase2() }.toMutableList()
            constructors.map(BoundFunction::semanticAnalysisPhase2).forEach(reportings::addAll)
            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase2).forEach(reportings::addAll)
            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = members.flatMap { it.semanticAnalysisPhase3() }.toMutableList()
            constructors.map(BoundFunction::semanticAnalysisPhase3).forEach(reportings::addAll)
            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)
            return@getResult reportings
        }
    }

    /*
        TODO: why are these two methods needed on a BaseType?
        Structs don't read/write, their member functions do. The member functions purity is validated
        against the struct boundary, not any other. These two methods shouldn't be returning anythin
        other than empty(), should they? Instead, the semanticAnalysisPhase3() needs to verify the
        purity of all member functions against the struct boundary.
         */
    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return members.flatMap { it.findReadsBeyond(boundary) }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return members.flatMap { it.findWritesBeyond(boundary) }
    }

    override fun resolveMemberVariable(name: String): ObjectMember? = members.find { it.name == name }
}