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
import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeEntry
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundBaseTypeMemberVariableAttributes
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.binding.basetype.BoundDeclaredBaseTypeMemberFunction
import compiler.binding.basetype.BoundSupertypeList
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeParameter.Companion.chain
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span

class BaseTypeDeclaration(
    val declarationKeyword: KeywordToken,
    val visibility: AstVisibility?,
    val name: IdentifierToken,
    val supertype: TypeReference?,
    val entryDeclarations: List<BaseTypeEntryDeclaration>,
    val typeParameters: List<TypeParameter>?,
) : AstFileLevelDeclaration {
    override val declaredAt = name.span

    fun bindTo(fileContext: CTContext): BoundBaseType {
        // declare this now to allow passing forward references to all children
        lateinit var boundTypeDef: BoundBaseType
        val typeDefAccessor = { boundTypeDef }

        val kind = when (declarationKeyword.keyword) {
            Keyword.CLASS_DEFINITION -> BoundBaseType.Kind.CLASS
            Keyword.INTERFACE_DEFINITION -> BoundBaseType.Kind.INTERFACE
            else -> throw InternalCompilerError("Unknown base type declaration keyword ${declarationKeyword.span}")
        }
        val typeVisibility = visibility?.bindTo(fileContext) ?: BoundVisibility.default(fileContext)
        val (boundTypeParameters, fileContextWithTypeParams) = typeParameters?.chain(fileContext) ?: Pair(null, fileContext)
        val typeRootContext = MutableCTContext(fileContextWithTypeParams, typeVisibility)
        val boundSupertypeList = BoundSupertypeList.bindSingleSupertype(supertype, typeRootContext, typeDefAccessor)
        val memberVariableInitializationContext = MutableExecutionScopedCTContext.functionRootIn(typeRootContext)
        fun buildSelfTypeReference(location: Span) = NamedTypeReference(
            simpleName = this.name.value,
            nullability = TypeReference.Nullability.NOT_NULLABLE,
            mutability = TypeMutability.READONLY,
            declaringNameToken = IdentifierToken(this.name.value, location),
            typeParameters?.map {
                AstSpecificTypeArgument(TypeVariance.UNSPECIFIED, NamedTypeReference(it.name))
            },
        )

        // the entries must retain their order, for semantic and linting reasons;
        // however, binding the member variables first enables the constructor code to be simpler
        val boundEntriesByAstNode = LinkedHashMap<BaseTypeEntryDeclaration, BoundBaseTypeEntry<*>>()
        entryDeclarations
            .asSequence()
            .filterIsInstance<BaseTypeMemberVariableDeclaration>()
            .associateWithTo(boundEntriesByAstNode) { it.bindTo(memberVariableInitializationContext, typeDefAccessor) }

        entryDeclarations
            .asSequence()
            .filter { it !in boundEntriesByAstNode }
            .associateWithTo(boundEntriesByAstNode) { entry ->
                when (entry) {
                    is BaseTypeConstructorDeclaration -> {
                        val boundMemberVars = boundEntriesByAstNode.values.asSequence()
                            .filterIsInstance<BoundBaseTypeMemberVariable>()
                            .toList()
                        entry.bindTo(fileContext, fileContextWithTypeParams, boundTypeParameters, boundMemberVars, typeDefAccessor)
                    }
                    is BaseTypeMemberFunctionDeclaration -> {
                        entry.bindTo(
                            typeRootContext,
                            buildSelfTypeReference(entry.functionDeclaration.parameters.parameters.firstOrNull()?.name?.span ?: entry.span),
                            typeDefAccessor
                        )
                    }
                    is BaseTypeDestructorDeclaration -> {
                        entry.bindTo(fileContext, fileContextWithTypeParams, boundTypeParameters, typeDefAccessor)
                    }
                    is BaseTypeMemberVariableDeclaration -> error("unreachable, member vars are done above")
                }
            }

        boundTypeDef = BoundBaseType(
            fileContext,
            typeRootContext,
            kind,
            typeVisibility,
            boundTypeParameters,
            boundSupertypeList,
            this,
            boundEntriesByAstNode.values.toList(),
        )
        return boundTypeDef
    }
}

sealed interface BaseTypeEntryDeclaration {
    val span: Span
}

sealed class BaseTypeMemberDeclaration : BaseTypeEntryDeclaration {
    abstract val name: IdentifierToken
}

class BaseTypeMemberVariableDeclaration(
    val attributes: List<KeywordToken>,
    val variableDeclaration: VariableDeclaration,
) : BaseTypeMemberDeclaration() {
    override val span = variableDeclaration.declaredAt
    override val name = variableDeclaration.name

    fun bindTo(context: ExecutionScopedCTContext, getTypeDef: () -> BoundBaseType): BoundBaseTypeMemberVariable {
        return BoundBaseTypeMemberVariable(
            context,
            this,
            BoundBaseTypeMemberVariableAttributes(attributes),
            getTypeDef,
        )
    }
}

class BaseTypeConstructorDeclaration(
    val attributes: List<AstFunctionAttribute>,
    val constructorKeyword: KeywordToken,
    val code: AstCodeChunk,
) : BaseTypeEntryDeclaration {
    override val span = constructorKeyword.span

    fun bindTo(
        parentContext: CTContext,
        parentContextWithTypeParameters: CTContext,
        typeParameters: List<BoundTypeParameter>?,
        boundMemberVariables: List<BoundBaseTypeMemberVariable>,
        getClassDef: () -> BoundBaseType
    ) : BoundClassConstructor {
        return BoundClassConstructor(parentContext, parentContextWithTypeParameters, typeParameters ?: emptyList(), boundMemberVariables, getClassDef, this)
    }
}

class BaseTypeDestructorDeclaration(
    val destructorKeyword: KeywordToken,
    val attributes: List<AstFunctionAttribute>,
    val code: AstCodeChunk,
) : BaseTypeEntryDeclaration {
    override val span = destructorKeyword.span

    fun bindTo(
        parentContext: CTContext,
        parentContextWithTypeParameters: CTContext,
        typeParameters: List<BoundTypeParameter>?,
        getClassDef: () -> BoundBaseType
    ): BoundClassDestructor {
        lateinit var dtor: BoundClassDestructor
        dtor = BoundClassDestructor(
            parentContext,
            parentContextWithTypeParameters,
            typeParameters ?: emptyList(),
            getClassDef,
            BoundFunctionAttributeList(parentContextWithTypeParameters, { dtor }, attributes),
            this
        )
        return dtor
    }
}

class BaseTypeMemberFunctionDeclaration(
    val functionDeclaration: FunctionDeclaration
) : BaseTypeMemberDeclaration() {
    override val span = functionDeclaration.declaredAt
    override val name = functionDeclaration.name

    fun bindTo(
        typeRootContext: CTContext,
        selfType: NamedTypeReference,
        getTypeDef: () -> BoundBaseType,
    ): BoundDeclaredBaseTypeMemberFunction {
        return functionDeclaration.bindToAsMember(
            typeRootContext,
            selfType,
            getTypeDef,
        )
    }
}