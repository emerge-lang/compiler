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

import compiler.InternalCompilerError
import compiler.reportings.Reporting
import java.util.*

/**
 * Connects all elements that make up a piece of software. Is able to resolve fully-qualified names across
 * contained [SourceFile]s.
 */
class SoftwareContext {
    /**
     * All the source files
     */
    private val sourceFiles: MutableSet<SourceFile> = HashSet()

    /**
     * @param names The single names of the module; e.g. for module `foo.bar.x` pass `["foo", "bar", "x"]`
     * @return The [CTContext] of the module with the given name or null if no such module is defined.
     *
     * TODO: rename to package, but that groups multiple files
     */
    fun module(vararg names: String): SourceFile? = sourceFiles.find { Arrays.equals(it.packageName, names) }

    fun module(name: Iterable<String>): SourceFile? = module(*name.toList().toTypedArray())

    /**
     * Defines a new module with the given name and the given context.
     * @throws InternalCompilerError If such a module is already defined.
     * TODO: Create & use a more specific exception
     */
    fun addSourceFile(sourceFile: SourceFile) {
        sourceFiles.add(sourceFile)
    }

    private var semanticAnaylsisReults: Collection<Reporting>? = null

    fun doSemanticAnalysis(): Collection<Reporting> {
        if (semanticAnaylsisReults == null) {
            semanticAnaylsisReults = (
                sourceFiles.flatMap(SourceFile::semanticAnalysisPhase1) +
                sourceFiles.flatMap(SourceFile::semanticAnalysisPhase2) +
                sourceFiles.flatMap(SourceFile::semanticAnalysisPhase3)).toSet()
        }

        return semanticAnaylsisReults!!
    }
}