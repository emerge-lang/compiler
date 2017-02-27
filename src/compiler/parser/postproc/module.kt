package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.*
import compiler.ast.context.Module
import compiler.ast.context.MutableCTContext
import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ModulePostProcessor(rule: Rule<List<MatchingResult<*>>>): (ModuleDeclaration) -> Rule<Module> {
    return { defaultDeclaration ->
        val converter = ModuleASTConverter(defaultDeclaration)

        rule
            .flatten()
            .map({ converter(it) })
    }
}

private class ModuleASTConverter(val defaultDeclaration: ModuleDeclaration) {
    operator fun invoke(inResult: MatchingResult<TransactionalSequence<Any, Position>>): MatchingResult<Module>
    {
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
                reportings.add(Reporting.error(
                    "Import declarations are not supported yet.",
                    declaration.declaredAt
                ))
            }
            else if (declaration is VariableDeclaration) {
                context.addVariable(declaration)
            }
            else if (declaration is FunctionDeclaration) {
                reportings.add(Reporting.error(
                    "Function declarations are not suppored yet.",
                    declaration.declaredAt
                ))
            }
            else {
                reportings.add(Reporting.error(
                    "Unsupported declaration $declaration",
                    declaration.declaredAt
                ))
            }
        }

        return MatchingResult(
            certainty = ResultCertainty.DEFINITIVE,
            result = Module(moduleDeclaration ?: defaultDeclaration, context),
            errors = inResult.errors.plus(reportings)
        )
    }
}