package compiler.parser

import compiler.ast.*
import compiler.diagnostic.ParsingErrorDiagnostic
import compiler.diagnostic.ReservedIdentifierDiagnostic
import compiler.diagnostic.UnsupportedFeatureDiagnostic
import compiler.lexer.*
import compiler.parser.grammar.SourceFileGrammar
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.github.tmarsteel.emerge.common.EmergeConstants

object SourceFileRule {
    fun match(tokens: Array<Token>, lexerFile: LexerSourceFile): MatchingResult<ASTSourceFile> {
        val inResult = matchAgainst(tokens, SourceFileGrammar)
        if (inResult is MatchingResult.Error) {
            return inResult
        }
        inResult as MatchingResult.Success

        val astSourceFile = ASTSourceFile(lexerFile)
        reportReservedIdentifiers(tokens, astSourceFile)

        inResult.item.forEachRemainingIndexed { index, declaration ->
            check(declaration is AstFileLevelDeclaration)

            if (declaration is ASTPackageDeclaration) {
                if (astSourceFile.selfDeclaration == null) {
                    if (index != 0) {
                        astSourceFile.addParseTimeReporting(
                            ParsingErrorDiagnostic(
                                "The package declaration must be the first declaration in the source file",
                                declaration.declaredAt
                            )
                        )
                    }

                    astSourceFile.selfDeclaration = declaration
                }
                else {
                    astSourceFile.addParseTimeReporting(
                        ParsingErrorDiagnostic(
                            "Duplicate package declaration",
                            declaration.declaredAt
                        )
                    )
                }
            }
            else if (declaration is AstImportDeclaration) {
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
                    UnsupportedFeatureDiagnostic(
                        "Unsupported declaration $declaration",
                        declaration.declaredAt,
                    )
                )
            }
        }

        if (astSourceFile.selfDeclaration == null) {
            astSourceFile.addParseTimeReporting(ParsingErrorDiagnostic(
                "No package declaration found.",
                (inResult.item.items.getOrNull(0) as AstFileLevelDeclaration?)?.declaredAt ?: Span.UNKNOWN
            ))
        }

        return MatchingResult.Success(astSourceFile, inResult.continueAtIndex)
    }

    private fun reportReservedIdentifiers(tokens: Array<Token>, astSourceFile: ASTSourceFile) {
        for (token in tokens) {
            val identifier = when (token) {
                is IdentifierToken -> token.value
                is DelimitedIdentifierContentToken -> token.content
                else -> continue
            }
            if (identifier.startsWith(EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX)) {
                astSourceFile.addParseTimeReporting(ReservedIdentifierDiagnostic(identifier, token.span))
            }
        }
    }
}
