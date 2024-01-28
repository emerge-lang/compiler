package compiler.parser

import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.StandardLibraryModule
import compiler.ast.ASTPackageDeclaration
import compiler.ast.ASTSourceFile
import compiler.ast.Declaration
import compiler.ast.FunctionDeclaration
import compiler.ast.ImportDeclaration
import compiler.ast.VariableDeclaration
import compiler.ast.struct.StructDeclaration
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.parser.grammar.SourceFileGrammar
import compiler.parser.grammar.rule.MatchingContext
import compiler.parser.grammar.rule.MatchingResult
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName

object SourceFileRule {
    fun match(tokens: TokenSequence, expectedPackageName: DotName): MatchingResult<ASTSourceFile> {
        val inResult = SourceFileGrammar.match(MatchingContext.None, tokens)
        @Suppress("UNCHECKED_CAST")
        val input = inResult.item ?: return inResult as MatchingResult<ASTSourceFile> // null can haz any type that i want :)

        val reportings: MutableSet<Reporting> = HashSet()
        val astSourceFile = ASTSourceFile(expectedPackageName)

        input.forEachRemainingIndexed { index, declaration ->
            declaration as? Declaration ?: throw InternalCompilerError("What tha heck went wrong here?!")

            if (declaration is ASTPackageDeclaration) {
                if (astSourceFile.selfDeclaration == null) {
                    if (index != 0) {
                        reportings.add(
                            Reporting.parsingError(
                            "The package declaration must be the first declaration in the source file",
                            declaration.declaredAt
                        ))
                    }

                    astSourceFile.selfDeclaration = declaration
                }
                else {
                    reportings.add(
                        Reporting.parsingError(
                        "Duplicate package declaration",
                        declaration.declaredAt
                    ))
                }
            }
            else if (declaration is ImportDeclaration) {
                astSourceFile.imports.add(declaration)
            }
            else if (declaration is VariableDeclaration) {
                astSourceFile.variables.add(declaration)
            }
            else if (declaration is FunctionDeclaration) {
                astSourceFile.functions.add(declaration)
            }
            else if (declaration is StructDeclaration) {
                astSourceFile.structs.add(declaration)
            }
            else {
                reportings.add(
                    Reporting.unsupported(
                    "Unsupported declaration $declaration",
                    declaration.declaredAt
                ))
            }
        }

        if (astSourceFile.selfDeclaration == null) {
            reportings.add(Reporting.parsingError("No package declaration found.", (input.items.getOrNull(0) as Declaration?)?.declaredAt ?: SourceLocation.UNKNOWN))
        }

        // default imports
        // TODO: refactor this into the binding code, its not part of the input sources
        astSourceFile.imports.add(
            ImportDeclaration(
                SourceLocation.UNKNOWN,
                (CoreIntrinsicsModule.NAME.components + "*").map(::IdentifierToken),
            )
        )
        astSourceFile.imports.add(
            ImportDeclaration(
                SourceLocation.UNKNOWN,
                (StandardLibraryModule.NAME.components + "*").map(::IdentifierToken),
            )
        )

        return MatchingResult(
            isAmbiguous = false,
            marksEndOfAmbiguity = inResult.marksEndOfAmbiguity,
            item = astSourceFile,
            reportings = inResult.reportings.plus(reportings)
        )
    }
}