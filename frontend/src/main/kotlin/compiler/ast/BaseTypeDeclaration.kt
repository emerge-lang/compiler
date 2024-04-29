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

import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.ast.AstSupertypeList.Companion.bindTo
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundBaseTypeEntry
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.binding.basetype.BoundDeclaredBaseTypeMemberFunction
import compiler.binding.basetype.BoundSupertypeList
import compiler.binding.basetype.SourceBoundSupertypeDeclaration
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeParameter.Companion.chain
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.SourceLocation

class BaseTypeDeclaration(
    val declarationKeyword: KeywordToken,
    val visibility: AstVisibility?,
    val name: IdentifierToken,
    val supertypes: AstSupertypeList?,
    val entryDeclarations: List<BaseTypeEntryDeclaration>,
    val typeParameters: List<TypeParameter>,
) : AstFileLevelDeclaration {
    override val declaredAt = name.sourceLocation

    fun bindTo(fileContext: CTContext): BoundBaseTypeDefinition {
        // declare this now to allow passing forward references to all children
        lateinit var boundTypeDef: BoundBaseTypeDefinition
        val typeDefAccessor = { boundTypeDef }

        val kind = when (declarationKeyword.keyword) {
            Keyword.CLASS_DEFINITION -> BoundBaseTypeDefinition.Kind.CLASS
            Keyword.INTERFACE_DEFINITION -> BoundBaseTypeDefinition.Kind.INTERFACE
            else -> throw InternalCompilerError("Unknown base type declaration keyword ${declarationKeyword.sourceLocation}")
        }
        val typeVisibility = visibility?.bindTo(fileContext) ?: BoundVisibility.default(fileContext)
        val (boundTypeParameters, fileContextWithTypeParams) = typeParameters.chain(fileContext)
        val typeRootContext = MutableCTContext(fileContextWithTypeParams, typeVisibility)
        val boundSupertypes = supertypes.bindTo(typeRootContext, name.sourceLocation, typeDefAccessor)
        val memberVariableInitializationContext = MutableExecutionScopedCTContext.functionRootIn(typeRootContext)
        val selfTypeReference = TypeReference(
            simpleName = this.name.value,
            nullability = TypeReference.Nullability.NOT_NULLABLE,
            mutability = TypeMutability.READONLY,
            declaringNameToken = this.name,
            typeParameters.map {
                TypeArgument(TypeVariance.UNSPECIFIED, TypeReference(it.name))
            },
        )

        // the entries must retain their order, for semantic and linting reasons
        val boundEntries = entryDeclarations
            .map<BaseTypeEntryDeclaration, BoundBaseTypeEntry<*>> { entry -> when (entry) {
                is BaseTypeMemberVariableDeclaration -> entry.bindTo(memberVariableInitializationContext)
                is BaseTypeConstructorDeclaration -> {
                    entry.bindTo(fileContextWithTypeParams, boundTypeParameters, typeDefAccessor)
                }
                is BaseTypeMemberFunctionDeclaration -> {
                    entry.bindTo(typeRootContext, selfTypeReference, typeDefAccessor)
                }
                is BaseTypeDestructorDeclaration -> {
                    entry.bindTo(fileContextWithTypeParams, boundTypeParameters, typeDefAccessor)
                }
            } }
            .toMutableList()

        boundTypeDef = BoundBaseTypeDefinition(
            fileContext,
            typeRootContext,
            kind,
            typeVisibility,
            boundTypeParameters,
            boundSupertypes,
            this,
            boundEntries,
        )
        return boundTypeDef
    }
}

data class AstSupertypeList(
    val typeRefs: List<TypeReference>,
) {
    companion object {
        fun AstSupertypeList?.bindTo(
            typeRootContext: CTContext,
            typeDeclaredAt: SourceLocation,
            getTypeDef: () -> BoundBaseTypeDefinition,
        ): BoundSupertypeList {
            val effectiveSupertypes = this?.typeRefs
                ?: listOf(TypeReference(IdentifierToken(CoreIntrinsicsModule.ANY_TYPE_NAME.simpleName, typeDeclaredAt.deriveGenerated())))
            val boundSupertypes = effectiveSupertypes.map { SourceBoundSupertypeDeclaration(typeRootContext, getTypeDef, it) }

            return BoundSupertypeList(boundSupertypes, getTypeDef)
        }
    }
}

/** TODO: rename to BaseTypeEntryDeclaration */
sealed interface BaseTypeEntryDeclaration {
    val sourceLocation: SourceLocation
}

sealed class BaseTypeMemberDeclaration : BaseTypeEntryDeclaration {
    abstract val name: IdentifierToken
}

class BaseTypeMemberVariableDeclaration(
    val variableDeclaration: VariableDeclaration,
) : BaseTypeMemberDeclaration() {
    override val sourceLocation = variableDeclaration.declaredAt
    override val name = variableDeclaration.name

    fun bindTo(context: ExecutionScopedCTContext): BoundBaseTypeMemberVariable {
        return BoundBaseTypeMemberVariable(
            context,
            this,
        )
    }
}

class BaseTypeConstructorDeclaration(
    val attributes: List<AstFunctionAttribute>,
    val constructorKeyword: IdentifierToken,
    val code: CodeChunk,
) : BaseTypeEntryDeclaration {
    override val sourceLocation = constructorKeyword.sourceLocation

    fun bindTo(fileContextWithTypeParameters: CTContext, typeParameters: List<BoundTypeParameter>, getClassDef: () -> BoundBaseTypeDefinition) : BoundClassConstructor {
        return BoundClassConstructor(fileContextWithTypeParameters, typeParameters, getClassDef, this)
    }
}

class BaseTypeDestructorDeclaration(
    val destructorKeyword: IdentifierToken,
    val code: CodeChunk,
) : BaseTypeEntryDeclaration {
    override val sourceLocation = destructorKeyword.sourceLocation

    fun bindTo(fileContextWithTypeParameters: CTContext, typeParameters: List<BoundTypeParameter>, getClassDef: () -> BoundBaseTypeDefinition): BoundClassDestructor {
        return BoundClassDestructor(fileContextWithTypeParameters, typeParameters, getClassDef, this)
    }
}

class BaseTypeMemberFunctionDeclaration(
    val functionDeclaration: FunctionDeclaration
) : BaseTypeMemberDeclaration() {
    override val sourceLocation = functionDeclaration.declaredAt
    override val name = functionDeclaration.name

    fun bindTo(
        typeRootContext: CTContext,
        selfType: TypeReference,
        getTypeDef: () -> BoundBaseTypeDefinition,
    ): BoundDeclaredBaseTypeMemberFunction {
        return functionDeclaration.bindToAsMember(
            typeRootContext,
            selfType,
            getTypeDef,
        )
    }
}