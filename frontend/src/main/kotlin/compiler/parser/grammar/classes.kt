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
import compiler.ast.ClassConstructorDeclaration
import compiler.ast.ClassDeclaration
import compiler.ast.ClassDestructorDeclaration
import compiler.ast.ClassEntryDeclaration
import compiler.ast.ClassMemberFunctionDeclaration
import compiler.ast.ClassMemberVariableDeclaration
import compiler.ast.CodeChunk
import compiler.ast.FunctionDeclaration
import compiler.ast.TypeParameterBundle
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeParameter
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.CLASS_DEFINITION
import compiler.lexer.KeywordToken
import compiler.lexer.Operator.CBRACE_CLOSE
import compiler.lexer.Operator.CBRACE_OPEN
import compiler.lexer.Operator.NEWLINE
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence

val ClassMemberVariableDeclaration = sequence("class member variable declaration") {
    ref(VariableDeclaration)
    operator(NEWLINE)
}
    .astTransformation { tokens ->
        ClassMemberVariableDeclaration(
            tokens.next() as VariableDeclaration,
        )
    }

val ClassMemberFunctionDeclaration = sequence("class member function declaration") {
    ref(StandaloneFunctionDeclaration)
}
    .astTransformation { tokens ->
        val decl = tokens.next() as FunctionDeclaration
        ClassMemberFunctionDeclaration(decl)
    }

val ClassConstructor = sequence("constructor declaration") {
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

        ClassConstructorDeclaration(
            attributes,
            ctorKeyword,
            code,
        )
    }

val ClassDestructor = sequence("destructor declaration") {
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

        ClassDestructorDeclaration(dtorKeyword, code)
    }

val ClassEntry = eitherOf {
    ref(ClassMemberVariableDeclaration)
    ref(ClassMemberFunctionDeclaration)
    ref(ClassConstructor)
    ref(ClassDestructor)
}
    .astTransformation { tokens -> tokens.remainingToList().single() as ClassEntryDeclaration }

val ClassDefinition = sequence("class definition") {
    optional {
        ref(Visibility)
    }
    keyword(CLASS_DEFINITION)
    identifier()
    optional {
        ref(BracedTypeParameters)
    }
    optionalWhitespace()
    operator(CBRACE_OPEN)
    optionalWhitespace()
    repeating {
        ref(ClassEntry)
        optionalWhitespace()
    }
    optionalWhitespace()
    operator(CBRACE_CLOSE)
    eitherOf {
        operator(NEWLINE)
        endOfInput()
    }
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

        ClassDeclaration(
            declarationKeyword.sourceLocation,
            visibility,
            name,
            entries,
            typeParameters,
        )
    }