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

import compiler.InternalCompilerError
import compiler.ast.AstPackageName
import compiler.ast.AstVisibility
import compiler.ast.VariableOwnership
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.*
import compiler.lexer.KeywordToken
import compiler.lexer.Operator.*
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence
import compiler.ast.Expression as AstExpression
import compiler.ast.VariableDeclaration as AstVariableDeclaration
import compiler.ast.VariableOwnership as AstVariableOwnership

val Visibility = eitherOf {
    keyword(PRIVATE)
    keyword(MODULE)
    sequence {
        keyword(PACKAGE)
        operator(PARANT_OPEN)
        ref(ModuleOrPackageName)
        operator(PARANT_CLOSE)
    }
    keyword(EXPORT)
}
    .astTransformation { tokens ->
        val visibilityToken = tokens.next() as KeywordToken
        when(visibilityToken.keyword) {
            PRIVATE -> AstVisibility.Private(visibilityToken)
            MODULE -> AstVisibility.Module(visibilityToken)
            EXPORT -> AstVisibility.Export(visibilityToken)
            PACKAGE -> {
                // skip parant_open
                tokens.next()
                val packageName = tokens.next() as AstPackageName
                AstVisibility.Package(visibilityToken, packageName)
            }
            else -> throw InternalCompilerError("grammar and ast builder mismatch")
        }
    }

val VariableDeclarationInitializingAssignment = sequence {
    operator(ASSIGNMENT)
    ref(Expression)
}

val VariableOwnership = eitherOf {
    keyword(BORROW)
    keyword(CAPTURE)
}
    .astTransformation { tokens ->
        val token = tokens.next() as KeywordToken
        val value = when(token.keyword) {
            BORROW -> AstVariableOwnership.BORROWED
            CAPTURE -> AstVariableOwnership.CAPTURED
            else -> throw InternalCompilerError("grammar and ast builder mismatch")
        }
        Pair(value, token)
    }

private val ReAssignableVariableDeclaration = sequence("re-assignable variable declaration") {
    optional {
        ref(Visibility)
    }
    optional {
        ref(VariableOwnership)
    }
    keyword(VAR)
    ref(Identifier)
    optional {
        operator(COLON)
        ref(Type)
    }
    optional {
        ref(VariableDeclarationInitializingAssignment)
    }
}

val FinalVariableDeclaration = sequence("final variable declaration") {
    optional {
        ref(Visibility)
    }
    optional {
        ref(VariableOwnership)
    }
    ref(Identifier)
    eitherOf {
        ref(VariableDeclarationInitializingAssignment)
        sequence {
            operator(COLON)
            ref(Type)
            optional {
                ref(VariableDeclarationInitializingAssignment)
            }
        }
    }
}

val VariableDeclaration = eitherOf("variable declaration") {
    ref(FinalVariableDeclaration)
    ref(ReAssignableVariableDeclaration)
}
    .astTransformation { tokens ->
        val visibility: AstVisibility?
        val ownership: Pair<VariableOwnership, KeywordToken>?
        val varKeywordToken: KeywordToken?

        var next = tokens.next()
        if (next is AstVisibility) {
            visibility = next
            next = tokens.next()
        } else {
            visibility = null
        }

        if (next is Pair<*, *>) {
            @Suppress("UNCHECKED_CAST")
            ownership = next as Pair<VariableOwnership, KeywordToken>
            next = tokens.next()
        } else {
            ownership = null
        }

        if (next is KeywordToken) {
            varKeywordToken = next
            next = tokens.next()
        } else {
            varKeywordToken = null
        }

        val nameToken = next as IdentifierToken


        var type: TypeReference? = null

        var colonOrAssignmentOp = tokens.next()

        if (colonOrAssignmentOp == OperatorToken(COLON)) {
            type = tokens.next()!! as TypeReference
            colonOrAssignmentOp = tokens.next()
        }

        var initializer: AstExpression? = null

        val assignmentOpOrNewline = colonOrAssignmentOp

        if (assignmentOpOrNewline == OperatorToken(ASSIGNMENT)) {
            initializer = tokens.next()!! as AstExpression
        }

        AstVariableDeclaration(
            (varKeywordToken?.span ?: nameToken.span) .. nameToken.span,
            visibility,
            varKeywordToken,
            ownership,
            nameToken,
            type,
            initializer
        )
    }