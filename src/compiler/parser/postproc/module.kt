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

package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.*
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.matching.ResultCertainty
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.reportings.Reporting
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ModulePostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<ASTModule> {
    return rule
        .flatten()
        .map(::toAST_Module)
}

private fun toAST_Module(inResult: RuleMatchingResult<TransactionalSequence<Any, Position>>): RuleMatchingResult<ASTModule> {
    @Suppress("UNCHECKED_CAST")
    val input = inResult.item ?: return inResult as RuleMatchingResult<ASTModule> // null can haz any type that i want :)

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
    astModule.imports.add(ImportDeclaration(SourceLocation.UNKNOWN, listOf(
        IdentifierToken("dotlin"),
        IdentifierToken("lang"),
        IdentifierToken("*")
    )))

    return RuleMatchingResultImpl(
        certainty = ResultCertainty.DEFINITIVE,
        item = astModule,
        reportings = inResult.reportings.plus(reportings)
    )
}