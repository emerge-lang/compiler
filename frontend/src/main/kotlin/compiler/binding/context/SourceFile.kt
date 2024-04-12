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

import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName
import compiler.lexer.SourceFile as LexerSourceFile

class SourceFile(
    val lexerFile: LexerSourceFile,
    val packageName: DotName,
    val context: SourceFileRootContext,
    /** [Reporting]s generated at bind-time: double declarations, ... */
    val bindTimeReportings: Collection<Reporting> = emptySet()
) {
    init {
        context.sourceFile = this
    }

    /**
     * Delegates to semantic analysis phase 1 of all components that make up this file;
     * collects the results and returns them. Also returns the [Reporting]s found when binding
     * elements to the file (such as doubly declared variables).
     */
    fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = bindTimeReportings.toMutableList()
        context.imports.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }
        context.types.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }
        context.variables.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }
        context.functions.forEach { reportings.addAll(it.semanticAnalysisPhase1()) }

        context.imports
            .asSequence()
            .filter { it.simpleName != null }
            .groupBy { it.simpleName!! }
            .values
            .filter { imports -> imports.size > 1 }
            .forEach { ambiguousImports ->
                reportings.add(Reporting.ambiguousImports(ambiguousImports))
            }

        return reportings
    }

    /**
     * Delegates to semantic analysis phase 2 of all components that make up this file;
     * collects the results and returns them.
     */
    fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = ArrayList<Reporting>()
        context.imports.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }
        context.types.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }
        context.variables.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }
        context.functions.forEach { reportings.addAll(it.semanticAnalysisPhase2()) }
        return reportings
    }

    /**
     * Delegates to semantic analysis phase 3 of all components that make up this file;
     * collects the results and returns them.
     */
    fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = ArrayList<Reporting>()
        context.imports.forEach { reportings.addAll(it.semanticAnalysisPhase3()) }
        context.types.forEach { reportings.addAll(it.semanticAnalysisPhase3()) }
        context.variables.forEach { reportings.addAll(it.semanticAnalysisPhase3()) }
        context.functions.forEach { reportings.addAll(it.semanticAnalysisPhase3()) }
        return reportings
    }
}