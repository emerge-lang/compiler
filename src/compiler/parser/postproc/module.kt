package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.*
import compiler.ast.context.Module
import compiler.ast.context.MutableCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ModulePostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Module> {
    return rule
        .flatten()
        .map(::toAST_Module)
}

private fun toAST_Module(inResult: MatchingResult<TransactionalSequence<Any, Position>>): MatchingResult<Module> {
    @Suppress("UNCHECKED_CAST")
    val input = inResult.result ?: return inResult as MatchingResult<Module> // null can haz any type that i want :)

    val context = MutableCTContext()
    val reportings: MutableSet<Reporting> = HashSet()
    var moduleDeclaration: ModuleDeclaration? = null

    input.forEachRemainingIndexed { index, declaration ->
        declaration as? Declaration ?: throw InternalCompilerError("What tha heck went wrong here?!")

        if (declaration is ModuleDeclaration) {
            if (moduleDeclaration == null) {
                if (index != 0) {
                    reportings.add(Reporting.error(
                        "The module declaration must be the first declaration in the source file",
                        declaration.declaredAt
                    ))
                }

                moduleDeclaration = declaration
            }
            else {
                reportings.add(Reporting.error(
                    "Duplicate module declaration",
                    declaration.declaredAt
                ))
            }
        }
        else if (declaration is ImportDeclaration) {
            context.addImport(declaration)
        }
        else if (declaration is VariableDeclaration) {
            context.addVariable(declaration)
        }
        else if (declaration is FunctionDeclaration) {
            context.addFunction(declaration)
        }
        else {
            reportings.add(Reporting.error(
                "Unsupported declaration $declaration",
                declaration.declaredAt
            ))
        }
    }

    if (moduleDeclaration == null) {
        reportings.add(Reporting.error("No module declaration found.", (input.items[0] as Declaration).declaredAt))
    }

    // default import dotlin.lang.*
    context.addImport(ImportDeclaration(SourceLocation.UNKNOWN, listOf(
        IdentifierToken("dotlin"),
        IdentifierToken("lang"),
        IdentifierToken("*")
    )))

    return MatchingResult(
        certainty = ResultCertainty.DEFINITIVE,
        result = Module(moduleDeclaration?.name ?: emptyArray<String>(), context),
        reportings = inResult.reportings.plus(reportings)
    )
}