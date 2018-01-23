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

package compiler.binding

import compiler.reportings.Reporting

/**
 * Assists elements with semantic analysis methods in managing the state of the analysis:
 * * assure that each phase is executed only once
 * * if a phase is called recursively, return an appropriate reporting
 */
class SemanticAnaylsisState {
    val phase1 = SemanticAnalysisPhaseState()
    val phase2 = SemanticAnalysisPhaseState()
    val phase3 = SemanticAnalysisPhaseState()
}

class SemanticAnalysisPhaseState {
    private var executing: Boolean = false
    private var result: Collection<Reporting>? = null

    /**
     * If the phase has already been executed, returns the cached results. If the phase is already executing,
     * returns an error that states the recursion error; otherwise, runs the given closure, stores the result and returns
     * the results.
     */
    fun synchronize(code: () -> Collection<Reporting>): Collection<Reporting> {
        if (executing) {
            return setOf(Reporting.semanticRecursion("Semantic recursion... i dont know how to get good error info in here yet..."))
        }

        if (result != null) {
            return result!!
        }

        this.executing = true

        try {
            val result = code()
            this.result = result
            return result
        }
        finally {
            this.executing = false
        }
    }
}