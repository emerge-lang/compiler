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

package compiler.binding.context

import compiler.binding.SemanticallyAnalyzable
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.ambiguousOrRedundantImports
import compiler.diagnostic.toplevelFunctionWithOverrideAttribute
import compiler.lexer.LexerSourceFile
import compiler.lexer.Operator

class SourceFile(
    val lexerFile: LexerSourceFile,
    val context: SourceFileRootContext,
    /** [Diagnostic]s generated at bind-time: double declarations, ... */
    val bindTimeDiagnosis: CollectingDiagnosis,
) : SemanticallyAnalyzable {
    init {
        context.sourceFile = this
    }

    /**
     * Delegates to semantic analysis phase 1 of all components that make up this file;
     * collects the results and returns them. Also returns the [Diagnostic]s found when binding
     * elements to the file (such as doubly declared variables).
     */
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        bindTimeDiagnosis.replayOnto(diagnosis)
        context.imports.forEach { it.semanticAnalysisPhase1(diagnosis) }
        context.types.forEach { it.semanticAnalysisPhase1(diagnosis) }
        context.variables.forEach { it.semanticAnalysisPhase1(diagnosis) }
        context.functions.forEach { it.semanticAnalysisPhase1(diagnosis) }

        context.imports
            .flatMap { import ->
                import.declaration.symbols.map { Pair(it.value, import) }
            }
            .filter { (simpleName, _) -> simpleName != Operator.TIMES.text }
            .groupBy(
                keySelector = { (simpleName, _) -> simpleName },
                valueTransform = { (_, import) -> import }
            )
            .filter { (_, imports) -> imports.size > 1 }
            .forEach { (simpleName, ambiguousImports) ->
                context.markSimpleNameAmbiguousByImports(simpleName)
                diagnosis.ambiguousOrRedundantImports(ambiguousImports, simpleName)
            }
    }

    /**
     * Delegates to semantic analysis phase 2 of all components that make up this file;
     * collects the results and returns them.
     */
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        context.imports.forEach { it.semanticAnalysisPhase2(diagnosis) }
        context.types.forEach { it.semanticAnalysisPhase2(diagnosis) }
        context.variables.forEach { it.semanticAnalysisPhase2(diagnosis) }
        context.functions.forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    /**
     * Delegates to semantic analysis phase 3 of all components that make up this file;
     * collects the results and returns them.
     */
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        context.imports.forEach { it.semanticAnalysisPhase3(diagnosis) }
        context.types.forEach { it.semanticAnalysisPhase3(diagnosis) }
        context.variables.forEach { it.semanticAnalysisPhase3(diagnosis) }
        context.functions.forEach { topLevelFn ->
            topLevelFn.semanticAnalysisPhase3(diagnosis)
            topLevelFn.attributes.firstOverrideAttribute?.let { overrideAttr ->
                diagnosis.toplevelFunctionWithOverrideAttribute(overrideAttr)
            }
        }
    }
}