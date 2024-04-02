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

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.classdef.BoundClassConstructor
import compiler.binding.classdef.BoundClassDefinition
import compiler.binding.classdef.BoundClassMemberFunction
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeParameter.Companion.chain
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class ClassDeclaration(
    override val declaredAt: SourceLocation,
    val visibility: AstVisibility?,
    val name: IdentifierToken,
    val entryDeclarations: List<ClassEntryDeclaration>,
    val typeParameters: List<TypeParameter>,
) : AstFileLevelDeclaration {
    fun bindTo(fileContext: CTContext): BoundClassDefinition {
        val (boundTypeParameters, fileContextWithTypeParams) = typeParameters.chain(fileContext)
        val classRootContext = MutableCTContext(fileContextWithTypeParams)
        val memberVariableInitializationContext = MutableExecutionScopedCTContext.functionRootIn(classRootContext)
        val selfTypeReference = TypeReference(
            simpleName = this.name.value,
            nullability = TypeReference.Nullability.NOT_NULLABLE,
            mutability = TypeMutability.READONLY,
            declaringNameToken = this.name,
            typeParameters.map {
                TypeArgument(TypeVariance.UNSPECIFIED, TypeReference(it.name))
            },
        )

        lateinit var boundClassDef: BoundClassDefinition
        var hasAtLeastOneConstructor = false
        // the entries must retain their order, for semantic and linting reasons
        val boundEntries = entryDeclarations
            .map { entry -> when (entry) {
                is ClassMemberVariableDeclaration -> entry.bindTo(memberVariableInitializationContext)
                is ClassConstructorDeclaration -> {
                    hasAtLeastOneConstructor = true
                    entry.bindTo(fileContextWithTypeParams, boundTypeParameters) { boundClassDef }
                }
                is ClassMemberFunctionDeclaration -> {
                    entry.bindTo(classRootContext, selfTypeReference)
                }
            } }
            .toMutableList()

        if (!hasAtLeastOneConstructor) {
            val defaultCtorAst = ClassConstructorDeclaration(emptyList(), IdentifierToken("constructor", declaredAt), CodeChunk(emptyList()))
            boundEntries.add(defaultCtorAst.bindTo(fileContextWithTypeParams, boundTypeParameters) { boundClassDef })
        }

        boundClassDef = BoundClassDefinition(
            fileContext,
            classRootContext,
            boundTypeParameters,
            this,
            boundEntries,
        )
        return boundClassDef
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
    val attributes: List<AstFunctionAttribute>,
    val constructorKeyword: IdentifierToken,
    val code: CodeChunk,
) : ClassEntryDeclaration {
    override val declaredAt = constructorKeyword.sourceLocation

    fun bindTo(fileContextWithTypeParameters: CTContext, typeParameters: List<BoundTypeParameter>, getClassDef: () -> BoundClassDefinition) : BoundClassConstructor {
        return BoundClassConstructor(fileContextWithTypeParameters, typeParameters, getClassDef, this)
    }
}

class ClassMemberFunctionDeclaration(
    val declaration: FunctionDeclaration
) : ClassMemberDeclaration() {
    override val declaredAt = declaration.declaredAt
    override val name = declaration.name

    fun bindTo(classRootContext: CTContext, selfType: TypeReference): BoundClassMemberFunction {
        return BoundClassMemberFunction(declaration.bindTo(classRootContext, selfType))
    }
}