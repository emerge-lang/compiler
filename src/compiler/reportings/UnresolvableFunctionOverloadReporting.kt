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

package compiler.reportings

import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken

/**
 * Reported when the target function of the invocation expression [expr] cannot be determined
 */
class UnresolvableFunctionOverloadReporting(
    val functionNameReference: IdentifierToken,
    val receiverType: BaseTypeReference?,
    val parameterTypes: List<BaseTypeReference?>,
    val functionDeclaredAtAll: Boolean,
) : Reporting(
    Level.ERROR,
    run {
        var message: String = if (functionDeclaredAtAll) {
            "Function ${functionNameReference.value} is not declared for types ${parameterTypes.typeTupleToString()}"
        } else {
            "Cannot resolve function or type ${functionNameReference.value}"
        }

        if (receiverType != null) {
            message += " on receiver of type $receiverType"
        }

        message
    },
    functionNameReference.sourceLocation,
)