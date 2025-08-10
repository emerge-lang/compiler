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

package compiler.diagnostic

import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.IdentifierToken

/**
 * Reported when the target function of the invocation expression [expr] cannot be determined
 */
class UnresolvableFunctionOverloadDiagnostic(
    val functionNameReference: IdentifierToken,
    val receiverType: BoundTypeReference?,
    val parameterTypes: List<BoundTypeReference?>,
    val functionDeclaredAtAll: Boolean,
    val inapplicableCandidates: List<InvocationCandidateNotApplicableDiagnostic>,
    val hasUnresolvableImportForFunctionName: Boolean,
) : Diagnostic(
    if (hasUnresolvableImportForFunctionName) Severity.CONSECUTIVE else Severity.ERROR,
    if (functionDeclaredAtAll) {
        "Function ${functionNameReference.value} is not declared for types ${parameterTypes.typeTupleToString()}"
    } else if (receiverType == null) {
        "Cannot resolve function or type ${functionNameReference.value}"
    } else {
        "Cannot resolve function ${functionNameReference.value} on receiver of type $receiverType"
    },
    functionNameReference.span,
) {
    init {
        check(inapplicableCandidates.isEmpty() || inapplicableCandidates.size > 1) {
            "in this case, we should be having just that single inapplicable diagnostic"
        }
    }

    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            super.renderBody()

            if (inapplicableCandidates.isNotEmpty()) {
                text("These functions could be invoked, but are not applicable:")
                sourceHints(inapplicableCandidates.map { it.inapplicabilityHint })
            }
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is UnresolvableFunctionOverloadDiagnostic) return false

        if (functionNameReference != other.functionNameReference) return false

        return true
    }

    override fun hashCode(): Int {
        return functionNameReference.hashCode()
    }
}