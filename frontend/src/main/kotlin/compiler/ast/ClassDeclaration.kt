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

package compiler.ast

import compiler.InternalCompilerError
import compiler.ast.type.TypeParameter
import compiler.binding.classdef.BoundClassDefinition
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class ClassDeclaration(
    override val declaredAt: SourceLocation,
    val name: IdentifierToken,
    val memberDeclarations: List<ClassMemberDeclaration>,
    val typeParameters: List<TypeParameter>,
) : AstFileLevelDeclaration {
    fun bindTo(context: CTContext): BoundClassDefinition {
        val classRootContext = MutableCTContext(context)
        val boundTypeParameters = typeParameters.map(classRootContext::addTypeParameter)
        val initializationContext = MutableExecutionScopedCTContext.functionRootIn(classRootContext)

        return BoundClassDefinition(
            context,
            classRootContext,
            boundTypeParameters,
            this,
            memberDeclarations.map {
                it as? ClassMemberVariableDeclaration
                    ?: throw InternalCompilerError("Class member functions not implemented yet")
                it.bindTo(initializationContext)
            },
        )
    }
}

sealed interface ClassEntryDeclaration {
    val declaredAt: SourceLocation
}

sealed class ClassMemberDeclaration : ClassEntryDeclaration {
    abstract val name: IdentifierToken
}

class ClassMemberVariableDeclaration(
    val variableDeclaration: VariableDeclaration,
) : ClassMemberDeclaration() {
    override val declaredAt = variableDeclaration.declaredAt
    override val name = variableDeclaration.name

    fun bindTo(context: ExecutionScopedCTContext): BoundClassMemberVariable {
        return BoundClassMemberVariable(
            context,
            this,
        )
    }
}

class ClassConstructorDeclaration(

)