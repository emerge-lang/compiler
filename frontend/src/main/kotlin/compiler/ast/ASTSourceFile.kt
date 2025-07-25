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

package compiler.ast

import compiler.InternalCompilerError
import compiler.binding.BoundImportDeclaration
import compiler.binding.context.ModuleContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.SoftwareContext
import compiler.binding.context.SourceFile
import compiler.binding.context.SourceFileRootContext
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.incorrectPackageDeclaration
import compiler.diagnostic.variableDeclaredMoreThanOnce
import compiler.lexer.IdentifierToken
import compiler.lexer.LexerSourceFile
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants

val DEFAULT_IMPORT_PACKAGES = listOf(
    EmergeConstants.CORE_MODULE_NAME,
    EmergeConstants.STD_MODULE_NAME,
)

/**
 * AST representation of a source file
 */
class ASTSourceFile(
    val lexerFile: LexerSourceFile,
) {
    val expectedPackageName = lexerFile.packageName

    var selfDeclaration: ASTPackageDeclaration? = null

    val imports: MutableList<AstImportDeclaration> = mutableListOf()

    val globalVariables: MutableList<VariableDeclaration> = mutableListOf()

    val functions: MutableList<FunctionDeclaration> = mutableListOf()

    val baseTypes: MutableList<BaseTypeDeclaration> = mutableListOf()

    private var parseTimeDiagnosis = CollectingDiagnosis()
    fun addParseTimeReporting(diagnostic: Diagnostic) {
        parseTimeDiagnosis.add(diagnostic)
    }

    /**
     * Works by the same principle as [Bindable.bindTo]; but since binds to a [SoftwareContext] (rather than a
     * [CTContext]) this has its own signature.
     */
    fun bindTo(context: ModuleContext): SourceFile {
        selfDeclaration?.packageName?.let { declaredPackageName ->
            if (declaredPackageName.names.map { it.value } != expectedPackageName.components) {
                parseTimeDiagnosis.incorrectPackageDeclaration(declaredPackageName, expectedPackageName)
            }
        }

        val packageContext = context.softwareContext.getPackage(expectedPackageName)
            ?: throw InternalCompilerError("Cannot bind source file in $expectedPackageName because its module hasn't been registered with the software-context yet.")
        val declaredPackage = selfDeclaration?.packageName?.names?.map(IdentifierToken::value)?.let(CanonicalElementName::Package) ?: expectedPackageName
        val fileContext = SourceFileRootContext(packageContext, declaredPackage)

        bindImportsInto(fileContext)
        bindFunctionsInto(fileContext)
        bindBaseTypesInto(fileContext)
        bindVariablesInto(fileContext, parseTimeDiagnosis)

        return SourceFile(
            lexerFile,
            fileContext,
            parseTimeDiagnosis
        )
    }

    private fun bindImportsInto(fileContext: SourceFileRootContext) {
        imports.forEach(fileContext::addImport)

        val defaultImportLocation = selfDeclaration?.declaredAt?.deriveGenerated()
            ?: Span(lexerFile, 1u, 1u, 1u, 1u, true)
        val defaultImports = DEFAULT_IMPORT_PACKAGES
            .map { pkgName ->
                AstImportDeclaration(
                    defaultImportLocation,
                    pkgName.components.map(::IdentifierToken),
                    listOf(IdentifierToken(BoundImportDeclaration.WILDCARD_SYMBOL)),
                )
            }

        for (defaultImport in defaultImports) {
            if (imports.any { it == defaultImport }) {
                continue
            }
            fileContext.addImport(defaultImport)
        }
    }

    private fun bindFunctionsInto(fileContext: SourceFileRootContext) {
        functions.forEach { fnDecl ->
            fileContext.addFunction(fnDecl.bindToAsTopLevel(fileContext))
        }
    }

    private fun bindBaseTypesInto(fileContext: SourceFileRootContext) {
        baseTypes.forEach(fileContext::addBaseType)
    }

    private fun bindVariablesInto(fileContext: SourceFileRootContext, diagnosis: Diagnosis) {
        val initializerContext = MutableExecutionScopedCTContext.functionRootIn(fileContext)

        for (globalVariable in globalVariables) {
            // check double declare
            val existingVariable = fileContext.resolveVariable(globalVariable.name.value, true)
            if (existingVariable == null || existingVariable.declaration === globalVariable) {
                fileContext.addVariable(globalVariable.bindToAsGlobalVariable(fileContext, initializerContext))
            }
            else {
                // variable double-declared
                diagnosis.variableDeclaredMoreThanOnce(existingVariable.declaration, globalVariable)
            }
        }
    }
}