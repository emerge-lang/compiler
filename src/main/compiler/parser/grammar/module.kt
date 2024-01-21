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
import compiler.ast.ASTModule
import compiler.ast.Declaration
import compiler.ast.FunctionDeclaration
import compiler.ast.ImportDeclaration
import compiler.ast.ModuleDeclaration
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
import java.util.ArrayList
import java.util.HashSet

val ModuleName = sequence("module or package name") {
    identifier()

    repeating {
        operator(Operator.DOT)
        identifier()
    }
}
    .astTransformation { tokens ->
        val identifiers = ArrayList<String>()

        while (tokens.hasNext()) {
            // collect the identifier
            identifiers.add((tokens.next()!! as IdentifierToken).value)

            // skip the dot, if there
            tokens.next()
        }

        identifiers.toTypedArray()
    }

val ModuleDeclaration = sequence("module declaration") {
    keyword(Keyword.MODULE)

    ref(ModuleName)

    operator(Operator.NEWLINE)
}
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken
        @Suppress("UNCHECKED_CAST") // ModuleName is a Rule<Array<String>>
        val moduleName = tokens.next()!! as Array<String>

        ModuleDeclaration(keyword.sourceLocation, moduleName)
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
            Reporting.parsingError("${it.message}; To import all exports of the module write module.*", it.sourceLocation)
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

val Module: Rule<ASTModule> = sequence("module") {
    repeatingAtLeastOnce {
        optionalWhitespace()
        eitherOf {
            endOfInput()
            ref(ModuleDeclaration)
            ref(ImportDeclaration)
            ref(VariableDeclaration)
            ref(StandaloneFunctionDeclaration)
            ref(StructDefinition)
        }
    }
    endOfInput()
}
    .flatten()
    .map { inResult ->
        @Suppress("UNCHECKED_CAST")
        val input = inResult.item ?: return@map inResult as MatchingResult<ASTModule> // null can haz any type that i want :)

        val reportings: MutableSet<Reporting> = HashSet()
        val astModule = ASTModule()

        input.forEachRemainingIndexed { index, declaration ->
            declaration as? Declaration ?: throw InternalCompilerError("What tha heck went wrong here?!")

            if (declaration is ModuleDeclaration) {
                if (astModule.selfDeclaration == null) {
                    if (index != 0) {
                        reportings.add(Reporting.parsingError(
                            "The module declaration must be the first declaration in the source file",
                            declaration.declaredAt
                        ))
                    }

                    astModule.selfDeclaration = declaration
                }
                else {
                    reportings.add(Reporting.parsingError(
                        "Duplicate module declaration",
                        declaration.declaredAt
                    ))
                }
            }
            else if (declaration is ImportDeclaration) {
                astModule.imports.add(declaration)
            }
            else if (declaration is VariableDeclaration) {
                astModule.variables.add(declaration)
            }
            else if (declaration is FunctionDeclaration) {
                astModule.functions.add(declaration)
            }
            else if (declaration is StructDeclaration) {
                astModule.structs.add(declaration)
            }
            else {
                reportings.add(Reporting.unsupported(
                    "Unsupported declaration $declaration",
                    declaration.declaredAt
                ))
            }
        }

        if (astModule.selfDeclaration == null) {
            reportings.add(Reporting.parsingError("No module declaration found.", (input.items.getOrNull(0) as Declaration?)?.declaredAt ?: SourceLocation.UNKNOWN))
        }

        // default import dotlin.lang.*
        astModule.imports.add(ImportDeclaration(
            SourceLocation.UNKNOWN, listOf(
            IdentifierToken("dotlin"),
            IdentifierToken("lang"),
            IdentifierToken("*")
        )))

        MatchingResult(
            isAmbiguous = false,
            marksEndOfAmbiguity = inResult.marksEndOfAmbiguity,
            item = astModule,
            reportings = inResult.reportings.plus(reportings)
        )
    }