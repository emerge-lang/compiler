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

package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BaseTypeReference
import compiler.reportings.Reporting

class BoundIdentifierExpression(
    override val context: CTContext,
    override val declaration: IdentifierExpression
) : BoundExpression<IdentifierExpression> {
    val identifier: String = declaration.identifier.value

    override val type: BaseTypeReference?
        get() = when(referredType) {
            ReferredType.VARIABLE -> referredVariable?.type
            ReferredType.TYPENAME -> referredBaseType?.baseReference?.invoke(context)
            null -> null
        }

    /** What this expression refers to; is null if not known */
    var referredType: ReferredType? = null
        private set

    /** The variable this expression refers to, if it does (see [referredType]); otherwise null. */
    var referredVariable: BoundVariable? = null
        private set

    /** The base type this expression referes to, if it does (see [referredType]); otherwise null. */
    var referredBaseType: BaseType? = null
        private set

    override var isGuaranteedToThrow = false

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // attempt variable
        val variable = context.resolveVariable(identifier)

        if (variable != null) {
            referredType = ReferredType.VARIABLE
            referredVariable = variable
        } else {
            var type: BaseType? = context.resolveDefinedType(identifier)
            if (type == null) {
                reportings.add(Reporting.undefinedIdentifier(declaration))
            } else {
                this.referredBaseType = type
                this.referredType = ReferredType.TYPENAME
            }
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (this.referredType == null) {
            // attempt a variable
            val variable = context.resolveVariable(identifier)
            if (variable != null) {
                referredVariable = variable
                referredType = ReferredType.VARIABLE
            }
            else {
                reportings.add(Reporting.error("Cannot resolve variable $identifier", declaration.sourceLocation))
            }
        }

        // TODO: attempt to resolve type; expression becomes of type "Type/Class", ... whatever, still to be defined

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        if (referredType == ReferredType.VARIABLE) {
            if (context.containsWithinBoundary(referredVariable!!, boundary)) {
                return emptySet()
            }
            else {
                return setOf(this)
            }
        }
        else {
            // TODO is reading type information of types declared outside the boundary considered impure?
            return emptySet() // no violation
        }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        // this does not write by itself; writs are done by other statements
        return emptySet()
    }

    /** The kinds of things an identifier can refer to. */
    enum class ReferredType {
        VARIABLE,
        TYPENAME
    }
}

