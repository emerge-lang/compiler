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

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeVariableNotUnderInferenceException
import compiler.binding.type.UnresolvedType
import compiler.binding.type.isAssignableTo
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

/**
 * Reported when a value of tye [sourceType] is to be written to a storage of type [targetType] and the types
 * are not compatible.
 */
open class ValueNotAssignableDiagnostic(
    /** The type of the storage area a value is to be written to; in an assignment its the type of the target variable */
    val targetType: BoundTypeReference,

    /** The type of the value that is to be written; in an assignments its the type of the expression to be written to a variable */
    val sourceType: BoundTypeReference,

    val reason: String,

    assignmentLocation: Span
) : Diagnostic(
    if (targetType is UnresolvedType || sourceType is UnresolvedType) Severity.CONSECUTIVE else Severity.ERROR,
    "Type mismatch: $reason",
    assignmentLocation
) {
    val simplifiedMessage: String? get() {
        val mutabilityUnconflictedSourceType = sourceType.withMutability(targetType.mutability)
        try {
            if (!(mutabilityUnconflictedSourceType isAssignableTo targetType)) {
                // error due to more than mutability => standard message is fine
                return null
            }
        }
        catch (ex: TypeVariableNotUnderInferenceException) {
            // the necessary context to reason about the types is gone
            return null
        }

        when (sourceType.mutability) {
            TypeMutability.MUTABLE -> when (targetType.mutability) {
                TypeMutability.IMMUTABLE -> return "A const value is needed here, this one is mut."
                TypeMutability.EXCLUSIVE -> return "An exclusive value is needed here, this one is mut."
                TypeMutability.READONLY,
                TypeMutability.MUTABLE -> throw InternalCompilerError("This should not have happened")
            }
            TypeMutability.READONLY -> when (targetType.mutability) {
                TypeMutability.MUTABLE -> return "Cannot mutate this value, this is a read reference."
                TypeMutability.EXCLUSIVE -> return "An exclusive value is needed here; this is a read reference."
                TypeMutability.READONLY -> throw InternalCompilerError("This should not have happened")
                TypeMutability.IMMUTABLE -> return "A const value is needed here. This is a read reference, immutability is not guaranteed."
            }
            TypeMutability.IMMUTABLE -> when (targetType.mutability) {
                TypeMutability.MUTABLE -> return "Cannot mutate this value. In fact, this is an const value."
                TypeMutability.EXCLUSIVE -> return "An exclusive value is needed here, this one is const."
                TypeMutability.READONLY,
                TypeMutability.IMMUTABLE -> throw InternalCompilerError("This should not have happened")
            }
            TypeMutability.EXCLUSIVE -> throw InternalCompilerError("This should not have happened")
        }
    }

    override val message: String get() = simplifiedMessage ?: super.message

    context(CellBuilder)
    override fun renderMessage() {
        text(message)
        horizontalLayout {
            column {
                text("Required:")
                text("Found:")
            }
            column {
                text(targetType.toString())
                text(sourceType.toString())
            }
        }
    }
}