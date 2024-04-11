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

package compiler.parser.grammar

import compiler.ast.AstFunctionAttribute
import compiler.ast.AstVisibility
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.BaseTypeDeclaration
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.BaseTypeMemberFunctionDeclaration
import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.ast.ClassEntryDeclaration
import compiler.ast.CodeChunk
import compiler.ast.FunctionDeclaration
import compiler.ast.TypeParameterBundle
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeParameter
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.CLASS_DEFINITION
import compiler.lexer.Keyword.INTERFACE_DEFINITION
import compiler.lexer.KeywordToken
import compiler.lexer.Operator.CBRACE_CLOSE
import compiler.lexer.Operator.CBRACE_OPEN
import compiler.lexer.Operator.NEWLINE
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence

val BaseTypeMemberVariableDeclaration = sequence("member variable declaration") {
    ref(VariableDeclaration)
    operator(NEWLINE)
}
    .astTransformation { tokens ->
        BaseTypeMemberVariableDeclaration(
            tokens.next() as VariableDeclaration,
        )
    }

val BaseTypeMemberFunctionDeclaration = sequence("member function declaration") {
    ref(StandaloneFunctionDeclaration)
}
    .astTransformation { tokens ->
        val decl = tokens.next() as FunctionDeclaration
        BaseTypeMemberFunctionDeclaration(decl)
    }

val BaseTypeConstructor = sequence("constructor declaration") {
    ref(FunctionAttributes)
    localKeyword("constructor")
    operator(CBRACE_OPEN)
    ref(CodeChunk)
    operator(CBRACE_CLOSE)
    operator(NEWLINE)
}
    .astTransformation { tokens ->
        val attributes = tokens.next() as List<AstFunctionAttribute>
        val ctorKeyword = tokens.next() as IdentifierToken
        tokens.next() as OperatorToken // skip CBRACE_OPEN
        val code = tokens.next() as CodeChunk

        BaseTypeConstructorDeclaration(
            attributes,
            ctorKeyword,
            code,
        )
    }

val BaseTypeDestructor = sequence("destructor declaration") {
    localKeyword("destructor")
    operator(CBRACE_OPEN)
    ref(CodeChunk)
    operator(CBRACE_CLOSE)
    operator(NEWLINE)
}
    .astTransformation { tokens ->
        val dtorKeyword = tokens.next() as IdentifierToken
        tokens.next() as OperatorToken // skip CBRACE_OPEN
        val code = tokens.next() as CodeChunk

        BaseTypeDestructorDeclaration(dtorKeyword, code)
    }

val BaseTypeEntry = eitherOf {
    ref(BaseTypeMemberVariableDeclaration)
    ref(BaseTypeMemberFunctionDeclaration)
    ref(BaseTypeConstructor)
    ref(BaseTypeDestructor)
}
    .astTransformation { tokens -> tokens.remainingToList().single() as ClassEntryDeclaration }

val BaseTypeDefinition = sequence("base type definition") {
    optional {
        ref(Visibility)
    }
    eitherOf {
        keyword(CLASS_DEFINITION)
        keyword(INTERFACE_DEFINITION)
    }
    identifier()
    optional {
        ref(BracedTypeParameters)
    }
    operator(CBRACE_OPEN)
    repeating {
        ref(BaseTypeEntry)
    }
    operator(CBRACE_CLOSE)
}
    .astTransformation { tokens ->
        val visibility: AstVisibility?
        var next: Any? = tokens.next()!!
        if (next is AstVisibility) {
            visibility = next
            next = tokens.next()!!
        } else {
            visibility = null
        }

        val declarationKeyword = next as KeywordToken // class keyword
        val name = tokens.next()!! as IdentifierToken

        next = tokens.next()
        val typeParameters: List<TypeParameter>
        if (next is TypeParameterBundle) {
            typeParameters = next.parameters
            tokens.next()!! // skip CBRACE_OPEN
        } else {
            check(next is OperatorToken)
            typeParameters = emptyList()
        }

        val entries = ArrayList<ClassEntryDeclaration>()

        next = tokens.next()!! // until CBRACE_CLOSE
        while (next is ClassEntryDeclaration) {
            entries += next
            next = tokens.next()
        }

        BaseTypeDeclaration(
            declarationKeyword,
            visibility,
            name,
            entries,
            typeParameters,
        )
    }