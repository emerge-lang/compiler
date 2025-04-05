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
import compiler.binding.BoundFunction
import compiler.binding.BoundVariableAssignmentStatement
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.expression.ValueUsage
import compiler.lexer.Span

data class PurityViolationDiagnostic(
    val impurity: Impurity,
    val boundary: SideEffectBoundary,
) : Diagnostic(
    Severity.ERROR,
    "${impurity.describe()} violates the purity of $boundary",
    impurity.span,
) {
    override fun toString(): String {
        val impurityHints = impurity.sourceHints
        if (impurityHints.isEmpty()) {
            return super.toString()
        }

        return "$levelAndMessage\n${illustrateHints(*impurityHints)}"
    }

    sealed class SideEffectBoundary {
        data class Function(val function: BoundFunction) : SideEffectBoundary() {
            override fun toString(): String {
                val modifier = if (BoundFunction.Purity.PURE.contains(function.purity)) "pure" else "readonly"
                val kindAndName = if (function is BoundClassConstructor) "constructor of class `${function.classDef.simpleName}`" else "function `${function.name}`"
                return "$modifier $kindAndName"
            }
        }

        data class ClassMemberInitializer(val member: BoundBaseTypeMemberVariable) : SideEffectBoundary() {
            override fun toString(): String {
                return "initializer of member variable `${member.name}`"
            }
        }
    }

    sealed interface Impurity {
        val span: Span
        val kind: ActionKind
        val sourceHints: Array<SourceHint>
            get() = arrayOf(SourceHint(span = span, description = null))

        fun describe(): String

        data class ReadingVariableBeyondBoundary(
            val readingExpression: BoundIdentifierExpression,
            val referral: BoundIdentifierExpression.ReferringVariable,
            val usage: ValueUsage
        ): Impurity {
            override val span = readingExpression.declaration.span
            override val kind = ActionKind.READ
            override fun describe(): String = usage.describeForDiagnostic('`' + referral.variable.name + '`')
        }

        data class ImpureInvocation(val invocation: BoundInvocationExpression, val functionToInvoke: BoundFunction) : Impurity {
            override val span = invocation.declaration.span
            override val kind = when (functionToInvoke.purity) {
                BoundFunction.Purity.PURE -> throw InternalCompilerError("Invoking a pure function cannot possibly be considered impure")
                BoundFunction.Purity.READONLY -> ActionKind.READ
                BoundFunction.Purity.MODIFYING -> ActionKind.MODIFY
            }
            override fun describe(): String = "invoking ${functionToInvoke.purity} function ${functionToInvoke.name}"
        }

        interface ReassignmentBeyondBoundary : Impurity {
            data class Variable(val assignment: BoundVariableAssignmentStatement) : ReassignmentBeyondBoundary {
                override val span = assignment.variableName.span
                override val kind = ActionKind.MODIFY
                override fun describe(): String = "assigning a new value to ${assignment.variableName.value}"
            }
            data class Complex(val assignmentTarget: BoundExpression<*>) : ReassignmentBeyondBoundary {
                override val span = assignmentTarget.declaration.span
                override val kind = ActionKind.MODIFY
                override fun describe(): String = "assigning a new value to this target"
            }
        }

        data class VariableUsedAsMutable(val referral: BoundIdentifierExpression.ReferringVariable, val usage: ValueUsage) : Impurity {
            override val span = referral.span
            override val kind = ActionKind.MODIFY
            override val sourceHints get() = arrayOf(
                SourceHint(span = referral.span, "`${referral.variable.name}` is used with a mut type here"),
                SourceHint(span = usage.span, "mut reference is created here"),
            )
            override fun describe() = usage.describeForDiagnostic("`" + referral.variable.name + "`")
        }
    }

    enum class ActionKind {
        READ,
        MODIFY,
        ;
    }
}