package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.*
import compiler.binding.context.Module
import compiler.binding.context.MutableCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResultImpl
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
                    reportings.add(Reporting.error(
                        "The module declaration must be the first declaration in the source file",
                        declaration.declaredAt
                    ))
                }

                astModule.selfDeclaration = declaration
            }
            else {
                reportings.add(Reporting.error(
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
            reportings.add(Reporting.error(
                "Unsupported declaration $declaration",
                declaration.declaredAt
            ))
        }
    }

    if (astModule.selfDeclaration == null) {
        reportings.add(Reporting.error("No module declaration found.", (input.items[0] as Declaration).declaredAt))
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