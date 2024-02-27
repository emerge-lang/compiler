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
import compiler.ast.Expression
import compiler.ast.InternalASTVisibilityModifier
import compiler.ast.PrivateASTVisibilityModifier
import compiler.ast.ProtectedASTVisibilityModifier
import compiler.ast.QualifiedASTProtectedVisibilityModifier
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.EXPORT
import compiler.lexer.Keyword.INTERNAL
import compiler.lexer.Keyword.PRIVATE
import compiler.lexer.Keyword.PROTECTED
import compiler.lexer.Keyword.VAR
import compiler.lexer.KeywordToken
import compiler.lexer.Operator.ASSIGNMENT
import compiler.lexer.Operator.COLON
import compiler.lexer.Operator.PARANT_CLOSE
import compiler.lexer.Operator.PARANT_OPEN
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.Rule

val VariableDeclarationInitializingAssignment = sequence {
    operator(ASSIGNMENT)
    optionalWhitespace()
    ref(Expression)
}

private val ReAssignableVariableDeclaration = sequence("re-assignable variable declaration") {
    keyword(VAR)
    identifier()
    optional {
        operator(COLON)
        ref(Type)
    }
    optional {
        ref(VariableDeclarationInitializingAssignment)
    }
}

val FinalVariableDeclaration = sequence("final variable declaration") {
    identifier()
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
        val varKeywordOrName = tokens.next()!!

        val varKeywordToken: KeywordToken?
        val nameToken: IdentifierToken

        if (varKeywordOrName is KeywordToken) {
            varKeywordToken = varKeywordOrName
            nameToken = tokens.next()!! as IdentifierToken
        }
        else {
            varKeywordToken = null
            nameToken = varKeywordOrName as IdentifierToken
        }

        var type: TypeReference? = null

        var colonOrAssignmentOp = tokens.next()

        if (colonOrAssignmentOp == OperatorToken(COLON)) {
            type = tokens.next()!! as TypeReference
            colonOrAssignmentOp = tokens.next()
        }

        var initializer: Expression? = null

        val assignmentOpOrNewline = colonOrAssignmentOp

        if (assignmentOpOrNewline == OperatorToken(ASSIGNMENT)) {
            initializer = tokens.next()!! as Expression
        }

        VariableDeclaration(
            varKeywordToken?.sourceLocation ?: nameToken.sourceLocation,
            varKeywordToken,
            nameToken,
            type,
            initializer
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
                ref(ModuleOrPackageName)
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
                @Suppress("UNCHECKED_CAST") // ModuleOrPackageName is a Rule<Array<String>>
                val qualifier = tokens.next()!! as Array<String>
                tokens.next()!! as OperatorToken // PARANT_CLOSE
                QualifiedASTProtectedVisibilityModifier(qualifier)
            } else {
                ProtectedASTVisibilityModifier.INSTANCE
            }
            else -> throw InternalCompilerError("Unknown visibility modifier keyword $keyword")
        }
    }
