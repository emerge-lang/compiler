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

import compiler.OnceAction
import compiler.ast.Executable
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.SourceFileRootContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinAny
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.handleCyclicInvocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAssignment
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

/**
 * Describes the presence/availability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class BoundVariable(
    override val context: CTContext,
    override val declaration: VariableDeclaration,
    val initializerExpression: BoundExpression<*>?,
    val kind: Kind,
) : BoundExecutable<VariableDeclaration> {
    val isAssignable: Boolean = declaration.isAssignable
    private val implicitMutability: TypeMutability = declaration.typeMutability
        ?: if (isAssignable) TypeMutability.MUTABLE else kind.defaultMutability

    val name: String = declaration.name.value
    private val isGlobal = context is SourceFileRootContext

    /**
     * The base type reference; null if not determined yet or if it cannot be determined due to semantic errors.
     */
    var type: BoundTypeReference? = null
        private set

    private var resolvedDeclaredType: BoundTypeReference? = null

    override val isGuaranteedToThrow: Boolean?
        get() = initializerExpression?.isGuaranteedToThrow

    private val onceAction = OnceAction()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            if (declaration.typeMutability != null && declaration.type != null) {
                reportings.add(Reporting.variableDeclaredWithSplitType(declaration))
            }

            context.resolveVariable(this.name)
                ?.takeUnless { it === this }
                ?.let { firstDeclarationOfVariable ->
                    reportings.add(
                        Reporting.variableDeclaredMoreThanOnce(
                            firstDeclarationOfVariable.declaration,
                            this.declaration
                        )
                    )
                }

            if (isGlobal && declaration.initializerExpression == null) {
                reportings.add(Reporting.globalVariableNotInitialized(this))
            }

            // type-related stuff
            // unknown type
            if (declaration.initializerExpression == null && declaration.type == null) {
                reportings.add(
                    Reporting.typeDeductionError(
                        "Cannot determine type of $kind $name; neither type nor initializer is specified.",
                        declaration.declaredAt
                    )
                )
            }

            declaration.type
                ?.let(context::resolveType)
                ?.defaultMutabilityTo(implicitMutability)
                ?.let { resolvedDeclaredType ->
                    this.resolvedDeclaredType = resolvedDeclaredType
                    this.type = resolvedDeclaredType
                }

            initializerExpression?.setExpectedEvaluationResultType(
                this.resolvedDeclaredType ?: BuiltinAny.baseReference
                    .withCombinedNullability(TypeReference.Nullability.NULLABLE)
                    .withMutability(implicitMutability)
            )

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
                handleCyclicInvocation(
                    context = this,
                    action = {
                        reportings.addAll(initializerExpression.semanticAnalysisPhase2())
                    },
                    onCycle = {
                        reportings.add(
                            Reporting.typeDeductionError(
                                "Cannot infer the type of variable $name because the type inference is cyclic here. Specify the type of one element explicitly.",
                                initializerExpression.declaration.sourceLocation
                            )
                        )
                    },
                )

                // if declaration doesn't mention mutability, try to infer it from the initializer
                // instead of using the default mutability
                var targetTypeToVerifyAgainst: BoundTypeReference? = null
                if (declaration.typeMutability == null && declaration.type?.mutability == null) {
                    type?.let { resolvedDeclaredType ->
                        initializerExpression.type?.let { initializerType ->
                            type = resolvedDeclaredType.withMutability(initializerType.mutability)
                            targetTypeToVerifyAgainst = type!!
                        }
                    }
                } else {
                    targetTypeToVerifyAgainst = resolvedDeclaredType
                }

                // verify compatibility declared type <-> initializer type
                if (targetTypeToVerifyAgainst != null) {
                    initializerExpression.type?.let { initializerType ->
                        // discrepancy between assign expression and declared type
                        if (initializerType !is UnresolvedType) {
                            initializerType.evaluateAssignabilityTo(targetTypeToVerifyAgainst!!, declaration.initializerExpression!!.sourceLocation)
                                ?.let(reportings::add)
                        }
                    }

                    // if the initializer type cannot be resolved the reporting is already done and
                    // should have returned it; so: we don't care :)
                }
            }

            // infer the type
            val initializerType = initializerExpression?.type
            if (type == null && initializerType != null) {
                if (declaration.typeMutability != null) {
                    if (!initializerType.mutability.isAssignableTo(declaration.typeMutability)) {
                        reportings.add(Reporting.valueNotAssignable(
                            initializerType.withMutability(declaration.typeMutability),
                            initializerType,
                            "Cannot assign a ${initializerType.mutability.name.lowercase()} value to a ${declaration.typeMutability.name.lowercase()} reference",
                            initializerExpression!!.declaration.sourceLocation,
                        ))
                    }
                    type = initializerType.withMutability(declaration.typeMutability)
                } else {
                    type = initializerType.withCombinedMutability(implicitMutability)
                }
            }

            if (type == null) {
                type = resolvedDeclaredType
            }

            if (resolvedDeclaredType != null) {
                val useSite = when (kind) {
                    Kind.VARIABLE -> TypeUseSite.Irrelevant
                    Kind.PARAMETER -> TypeUseSite.InUsage(declaration.sourceLocation)
                }
                resolvedDeclaredType!!.validate(useSite).let(reportings::addAll)
            }

            return@getResult reportings
        }
    }

    override val modifiedContext: CTContext by lazy {
        val newCtx = MutableCTContext(context)
        newCtx.addVariable(this)
        if (initializerExpression != null) {
            newCtx.markVariableInitialized(this)
        }
        newCtx
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return initializerExpression?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return initializerExpression?.findWritesBeyond(boundary) ?: emptySet()
    }

    fun isInitializedInContext(context: CTContext): Boolean {
        return isGlobal || kind == Kind.PARAMETER || context.initializesVariable(this)
    }

    val backendIrDeclaration: IrVariableDeclaration by lazy { IrVariableDeclarationImpl(name, type!!.toBackendIr()) }

    override fun toBackendIr(): IrExecutable {
        if (initializerExpression == null) {
            return backendIrDeclaration
        }

        return IrCodeChunkImpl(listOf(
            backendIrDeclaration,
            IrVariableAssignmentImpl(backendIrDeclaration, initializerExpression.toBackendIr())
        ))
    }

    enum class Kind(
        val defaultMutability: TypeMutability,
    ) {
        VARIABLE(TypeMutability.IMMUTABLE),
        PARAMETER(TypeMutability.READONLY),
        ;

        override fun toString() = name.lowercase()
    }
}

private class IrVariableDeclarationImpl(
    override val name: String,
    override val type: IrType,
) : IrVariableDeclaration

private class IrVariableAssignmentImpl(
    override val declaration: IrVariableDeclaration,
    override val value: IrExpression,
) : IrVariableAssignment