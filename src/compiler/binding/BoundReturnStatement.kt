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
import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.ResolvedTypeReference
import compiler.reportings.Reporting

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement
) : BoundExecutable<ReturnStatement> {

    private var expectedReturnType: ResolvedTypeReference? = null

    val expression = declaration.expression.bindTo(context)

    var returnType: ResolvedTypeReference? = null
        private set

    override val isGuaranteedToReturn = true // this is the core LoC that makes the property work big-scale
    override val mayReturn = true            // this is the core LoC that makes the property work big-scale

    override val isGuaranteedToThrow = expression.isGuaranteedToThrow

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return expression.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return expression.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings += expression.semanticAnalysisPhase3()

        val expectedReturnType = this.expectedReturnType
            ?: return reportings + Reporting.consecutive("Cannot check return value type because the expected return type is not known", declaration.sourceLocation)
        val expressionType = expression.type

        if (expressionType != null) {
            if (!(expressionType isAssignableTo expectedReturnType)) {
                reportings += Reporting.returnTypeMismatch(expectedReturnType, expressionType, declaration.sourceLocation)
            }
        }

        return reportings
    }

    override fun setExpectedReturnType(type: ResolvedTypeReference) {
        expectedReturnType = type
    }
}