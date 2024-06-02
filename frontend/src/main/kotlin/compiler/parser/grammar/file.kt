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

import compiler.ast.ASTPackageDeclaration
import compiler.ast.AstPackageName
import compiler.ast.ImportDeclaration
import compiler.ast.VariableDeclaration
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.TokenEqualToRule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

val ModuleOrPackageName = sequence("module or package name") {
    ref(Identifier)

    repeating {
        operator(Operator.DOT)
        ref(Identifier)
    }
}
    .astTransformation { tokens ->
        val identifiers = ArrayList<IdentifierToken>()

        while (tokens.hasNext()) {
            // collect the identifier
            identifiers.add(tokens.next()!! as IdentifierToken)

            // skip the dot, if there
            tokens.next()
        }

        AstPackageName(identifiers)
    }

val PackageDeclaration = sequence("package declaration") {
    keyword(Keyword.PACKAGE)

    ref(ModuleOrPackageName)

    operator(Operator.NEWLINE)
}
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken
        @Suppress("UNCHECKED_CAST") // ModuleOrPackageName is a Rule<Array<String>>
        val packageName = tokens.next()!! as AstPackageName

        ASTPackageDeclaration(keyword, packageName)
    }

val ImportDeclaration = sequence("import declaration") {
    keyword(Keyword.IMPORT)

    repeatingAtLeastOnce {
        ref(Identifier)
        operator(Operator.DOT)
    }
    eitherOf {
        ref(Identifier)
        ref(TokenEqualToRule(OperatorToken(Operator.TIMES)).mapResult { IdentifierToken((it as OperatorToken).operator.text, it.span) })
    }
    operator(Operator.NEWLINE)
}
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken

        val identifiers = ArrayList<IdentifierToken>()

        while (tokens.hasNext()) {
            // collect the identifier
            identifiers.add(tokens.next()!! as IdentifierToken)

            // skip the dot, if there
            tokens.next()
        }

        ImportDeclaration(keyword.span, identifiers)
    }

val TopLevelVariableDeclaration = sequence("toplevel variable declaration") {
    ref(VariableDeclaration)
    operator(Operator.NEWLINE)
}
    .astTransformation { tokens -> tokens.next()!! as VariableDeclaration }

val SourceFileGrammar: Rule<TransactionalSequence<Any, Position>> = sequence("source file") {
    repeatingAtLeastOnce {
        eitherOf {
            ref(PackageDeclaration)
            ref(ImportDeclaration)
            ref(TopLevelVariableDeclaration)
            ref(StandaloneFunctionDeclaration)
            ref(BaseTypeDefinition)
        }
    }
    endOfInput()
}
    .flatten()