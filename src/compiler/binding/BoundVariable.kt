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

import compiler.EarlyStackOverflowException
import compiler.OnceAction
import compiler.ast.Executable
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeMutability
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.ResolvedTypeReference
import compiler.binding.type.UnresolvedType
import compiler.reportings.Reporting
import compiler.throwOnCycle

/**
 * Describes the presence/avaiability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class BoundVariable(
    override val context: CTContext,
    override val declaration: VariableDeclaration,
    val initializerExpression: BoundExpression<*>?
) : BoundExecutable<VariableDeclaration>
{
    val isAssignable: Boolean = declaration.isAssignable
    private val implicitMutability: TypeMutability = if (isAssignable) TypeMutability.MUTABLE else TypeMutability.IMMUTABLE

    val name: String = declaration.name.value

    /**
     * The base type reference; null if not determined yet or if it cannot be determined due to semantic errors.
     */
    var type: ResolvedTypeReference? = null
        private set

    override val isGuaranteedToThrow: Boolean?
        get() = initializerExpression?.isGuaranteedToThrow

    private val onceAction = OnceAction()

    override fun semanticAnalysisPhase1() = semanticAnalysisPhase1("variable")

    fun semanticAnalysisPhase1(selfType: String): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            if (declaration.typeMutability != null && declaration.type != null) {
                reportings.add(Reporting.variableDeclaredWithSplitType(declaration))
            }

            context.resolveVariable(this.name)
                ?.takeUnless { it == this }
                ?.let { firstDeclarationOfVariable ->
                    reportings.add(
                        Reporting.variableDeclaredMoreThanOnce(
                            firstDeclarationOfVariable.declaration,
                            this.declaration
                        )
                    )
                }

            // TODO: warn about shadowing

            // type-related stuff
            // unknown type
            if (declaration.initializerExpression == null && declaration.type == null) {
                reportings.add(
                    Reporting.typeDeductionError(
                        "Cannot determine type of $selfType $name; neither type nor initializer is specified.",
                        declaration.declaredAt
                    )
                )
            }

            declaration.type?.let { declaredType ->
                val resolvedDeclaredType = context.resolveType(declaredType)
                resolvedDeclaredType?.validate()?.let(reportings::addAll)
                type = resolvedDeclaredType?.withCombinedMutability(implicitMutability)
            }

            if (initializerExpression != null) {
                reportings.addAll(initializerExpression.semanticAnalysisPhase1())
            }

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = mutableSetOf<Reporting>()

            if (initializerExpression != null) {
                try {
                    throwOnCycle(this) {
                        reportings.addAll(initializerExpression.semanticAnalysisPhase2())
                    }
                } catch (ex: EarlyStackOverflowException) {
                    reportings.add(
                        Reporting.typeDeductionError(
                            "Cannot infer the type of variable $name because the type inference is cyclic here. Specify the type of one element explicitly.",
                            initializerExpression.declaration.sourceLocation
                        )
                    )
                }

                initializerExpression.type?.validate()?.let(reportings::addAll)

                // verify compatibility declared type <-> initializer type
                if (type != null) {
                    val initializerType = initializerExpression.type

                    // if the initializer type cannot be resolved the reporting is already done and
                    // should have returned it; so: we don't care :)

                    // discrepancy between assign expression and declared type
                    if (initializerType != null) {
                        if (initializerType !is UnresolvedType) {
                            initializerType.evaluateAssignabilityTo(type!!, declaration.initializerExpression!!.sourceLocation)
                                ?.let(reportings::add)
                        }
                    }
                }

                // TODO: discrepancy between implied modifiers of initializerExpression and type modifiers of this declaration
            }

            // infer the type
            val initializerType = initializerExpression?.type
            if (type == null && initializerType != null) {
                if (declaration.typeMutability != null) {
                    if (!initializerType.mutability.isAssignableTo(declaration.typeMutability)) {
                        reportings.add(Reporting.valueNotAssignable(
                            initializerType.modifiedWith(declaration.typeMutability),
                            initializerType,
                            "Cannot assign a ${initializerType.mutability.name.lowercase()} value to a ${declaration.typeMutability.name.lowercase()} reference",
                            initializerExpression!!.declaration.sourceLocation,
                        ))
                    }
                    type = initializerType.modifiedWith(declaration.typeMutability)
                } else {
                    type = initializerType.withCombinedMutability(implicitMutability)
                }
            }

            return@getResult reportings
        }
    }

    override val modifiedContext: CTContext by lazy {
        val newCtx = MutableCTContext(context)
        newCtx.addVariable(this)
        newCtx
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return initializerExpression?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return initializerExpression?.findWritesBeyond(boundary) ?: emptySet()
    }
}