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
import compiler.PackageName
import compiler.ast.ASTSourceFile
import compiler.ast.Declaration
import compiler.ast.FunctionDeclaration
import compiler.ast.ImportDeclaration
import compiler.ast.ASTPackageDeclaration
import compiler.ast.ASTPackageName
import compiler.ast.VariableDeclaration
import compiler.ast.struct.StructDeclaration
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.SourceLocation
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.enhanceErrors
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.map
import compiler.parser.grammar.dsl.sequence
import compiler.reportings.ParsingMismatchReporting
import compiler.reportings.Reporting
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.ArrayList
import java.util.HashSet

val ModuleOrPackageName = sequence("module or package name") {
    identifier()

    repeating {
        operator(Operator.DOT)
        identifier()
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

        ASTPackageName(identifiers)
    }

val PackageDeclaration = sequence("package declaration") {
    keyword(Keyword.PACKAGE)

    ref(ModuleOrPackageName)

    operator(Operator.NEWLINE)
}
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken
        @Suppress("UNCHECKED_CAST") // ModuleOrPackageName is a Rule<Array<String>>
        val packageName = tokens.next()!! as ASTPackageName

        ASTPackageDeclaration(keyword, packageName)
    }

val ImportDeclaration = sequence("import declaration") {
    keyword(Keyword.IMPORT)

    repeatingAtLeastOnce {
        identifier()
        operator(Operator.DOT)
    }
    identifier(acceptedOperators = listOf(Operator.TIMES))
    operator(Operator.NEWLINE)
}
    .enhanceErrors(
        { it is ParsingMismatchReporting && it.expected == "operator dot" && it.actual == "operator newline" },
        {
            Reporting.parsingError("${it.message}; To import all exports of the package write some_package.*", it.sourceLocation)
        }
    )
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken

        val identifiers = ArrayList<IdentifierToken>()

        while (tokens.hasNext()) {
            // collect the identifier
            identifiers.add(tokens.next()!! as IdentifierToken)

            // skip the dot, if there
            tokens.next()
        }

        ImportDeclaration(keyword.sourceLocation, identifiers)
    }

val SourceFileGrammar: Rule<TransactionalSequence<Any, Position>> = sequence("source file") {
    repeatingAtLeastOnce {
        optionalWhitespace()
        eitherOf {
            endOfInput()
            ref(PackageDeclaration)
            ref(ImportDeclaration)
            ref(VariableDeclaration)
            ref(StandaloneFunctionDeclaration)
            ref(StructDefinition)
        }
    }
    endOfInput()
}
    .flatten()