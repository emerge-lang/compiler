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

import compiler.InternalCompilerError
import compiler.ast.CodeChunk
import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.type.ResolvedTypeReference
import compiler.reportings.Reporting
import compiler.handleCyclicInvocation

class BoundCodeChunk(
    /**
     * Context that applies to the leftHandSide statement; derivatives are stored within the statements themselves
     */
    override val context: CTContext,

    override val declaration: CodeChunk
) : BoundExecutable<CodeChunk> {

    private var expectedReturnType: ResolvedTypeReference? = null

    /** The bound statements of this code; must not be null after semantic analysis is done */
    var statements: List<BoundExecutable<*>>? = null
        private set

    override val isGuaranteedToThrow: Boolean?
        get() = statements?.any { it.isGuaranteedToThrow ?: false }

    override val isGuaranteedToReturn: Boolean?
        get() = statements?.any { it.isGuaranteedToReturn ?: false }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        var currentContext = context
        val boundStatements = mutableListOf<BoundExecutable<*>>()

        for (astStatement in declaration.statements) {
            val boundStatement = astStatement.bindTo(currentContext)

            if (this.expectedReturnType != null) {
                boundStatement.setExpectedReturnType(this.expectedReturnType!!)
            }

            reportings += boundStatement.semanticAnalysisPhase1()
            reportings += boundStatement.semanticAnalysisPhase2()
            reportings += boundStatement.semanticAnalysisPhase3()

            boundStatements.add(boundStatement)
            currentContext = boundStatement.modifiedContext
        }

        this.statements = boundStatements

        return reportings
    }

    override fun setExpectedReturnType(type: ResolvedTypeReference) {
        this.expectedReturnType = type
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        if (statements == null) throw InternalCompilerError("Illegal state: invoke this function after semantic analysis phase 3 is completed.")

        return statements!!.flatMap {
            handleCyclicInvocation(
                context = this,
                action =  { it.findReadsBeyond(boundary) },
                onCycle = ::emptySet,
            )
        }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        if (statements == null) throw InternalCompilerError("Illegal state: invoke this function after semantic analysis phase 3 is completed.")

        return statements!!.flatMap {
            handleCyclicInvocation(
                context = this,
                action = { it.findWritesBeyond(boundary) },
                onCycle = ::emptySet,
            )
        }
    }
}
