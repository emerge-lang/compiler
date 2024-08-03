package compiler.parser

import compiler.ast.ASTPackageDeclaration
import compiler.ast.ASTSourceFile
import compiler.ast.AstFileLevelDeclaration
import compiler.ast.BaseTypeDeclaration
import compiler.ast.FunctionDeclaration
import compiler.ast.ImportDeclaration
import compiler.ast.VariableDeclaration
import compiler.lexer.Span
import compiler.lexer.Token
import compiler.parser.grammar.SourceFileGrammar
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import compiler.reportings.Reporting
import compiler.lexer.SourceFile as LexerSourceFile

object SourceFileRule {
    fun match(tokens: Array<Token>, lexerFile: LexerSourceFile): MatchingResult<ASTSourceFile> {
        val inResult = matchAgainst(tokens, SourceFileGrammar)
        if (inResult is MatchingResult.Error) {
            return inResult
        }
        inResult as MatchingResult.Success

        val astSourceFile = ASTSourceFile(lexerFile)

        inResult.item.forEachRemainingIndexed { index, declaration ->
            check(declaration is AstFileLevelDeclaration)

            if (declaration is ASTPackageDeclaration) {
                if (astSourceFile.selfDeclaration == null) {
                    if (index != 0) {
                        astSourceFile.addParseTimeReporting(
                            Reporting.parsingError(
                            "The package declaration must be the first declaration in the source file",
                            declaration.declaredAt
                        ))
                    }

                    astSourceFile.selfDeclaration = declaration
                }
                else {
                    astSourceFile.addParseTimeReporting(
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
                astSourceFile.globalVariables.add(declaration)
            }
            else if (declaration is FunctionDeclaration) {
                astSourceFile.functions.add(declaration)
            }
            else if (declaration is BaseTypeDeclaration) {
                astSourceFile.baseTypes.add(declaration)
            }
            else {
                astSourceFile.addParseTimeReporting(
                    Reporting.unsupported(
                    "Unsupported declaration $declaration",
                    declaration.declaredAt,
                ))
            }
        }

        if (astSourceFile.selfDeclaration == null) {
            astSourceFile.addParseTimeReporting(Reporting.parsingError(
                "No package declaration found.",
                (inResult.item.items.getOrNull(0) as AstFileLevelDeclaration?)?.declaredAt ?: Span.UNKNOWN
            ))
        }

        return MatchingResult.Success(astSourceFile, inResult.continueAtIndex)
    }
}