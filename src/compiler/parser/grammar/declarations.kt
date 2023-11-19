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
import compiler.ast.ASTVisibilityModifier
import compiler.ast.ExportASTVisibilityModifier
import compiler.ast.InternalASTVisibilityModifier
import compiler.ast.PrivateASTVisibilityModifier
import compiler.ast.ProtectedASTVisibilityModifier
import compiler.ast.QualifiedASTProtectedVisibilityModifier
import compiler.ast.VariableDeclaration
import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.*
import compiler.lexer.KeywordToken
import compiler.lexer.Operator.*
import compiler.lexer.OperatorToken
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.dsl.eitherOf

val VariableDeclaration = sequence("variable declaration") {

    optional {
        ref(TypeModifier)
    }

    optionalWhitespace()

    eitherOf {
        keyword(VAR)
        keyword(VAL)
    }

    optionalWhitespace()

    identifier()

    optional {
        operator(COLON)
        ref(Type)
    }

    optional {
        optionalWhitespace()
        operator(ASSIGNMENT)
        ref(Expression)
    }
}
    .astTransformation { tokens ->
        val modifierOrKeyword = tokens.next()!!

        val typeModifier: TypeModifier?
        val declarationKeyword: KeywordToken

        if (modifierOrKeyword is TypeModifier) {
            typeModifier = modifierOrKeyword
            declarationKeyword = tokens.next()!! as KeywordToken
        }
        else {
            typeModifier = null
            declarationKeyword = modifierOrKeyword as KeywordToken
        }

        val name = tokens.next()!! as IdentifierToken

        var type: TypeReference? = null

        var colonOrEqualsOrNewline = tokens.next()

        if (colonOrEqualsOrNewline == OperatorToken(COLON)) {
            type = tokens.next()!! as TypeReference
            colonOrEqualsOrNewline = tokens.next()
        }

        var assignExpression: Expression<*>? = null

        val equalsOrNewline = colonOrEqualsOrNewline

        if (equalsOrNewline == OperatorToken(ASSIGNMENT)) {
            assignExpression = tokens.next()!! as Expression<*>
        }

        VariableDeclaration(
            declarationKeyword.sourceLocation,
            typeModifier,
            name,
            type,
            declarationKeyword.keyword == VAR,
            assignExpression
        )
    }

val VisibilityModifier : Rule<ASTVisibilityModifier> = eitherOf("visibility modifier") {
    eitherOf {
        keyword(PRIVATE)
        keyword(PROTECTED)
        keyword(EXPORT)
        sequence {
            keyword(INTERNAL)
            optional {
                operator(PARANT_OPEN)
                ref(ModuleName)
                operator(PARANT_CLOSE)
            }
        }
    }
}
    .astTransformation { tokens ->
        when (val keyword = (tokens.next()!! as KeywordToken).keyword) {
            PRIVATE -> PrivateASTVisibilityModifier.INSTANCE
            INTERNAL -> InternalASTVisibilityModifier.INSTANCE
            EXPORT -> ExportASTVisibilityModifier.INSTANCE
            PROTECTED -> if (tokens.hasNext()) {
                tokens.next()!! as OperatorToken // PARANT_OPEN
                val qualifier = tokens.next()!! as Array<String>
                tokens.next()!! as OperatorToken // PARANT_CLOSE
                QualifiedASTProtectedVisibilityModifier(qualifier)
            } else {
                ProtectedASTVisibilityModifier.INSTANCE
            }
            else -> throw InternalCompilerError("Unknown visibility modifier keyword $keyword")
        }
    }
