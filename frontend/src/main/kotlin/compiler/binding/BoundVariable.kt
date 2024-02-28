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
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.SourceFileRootContext
import compiler.binding.expression.BoundExpression
import compiler.binding.misc_ir.IrCreateReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinAny
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.handleCyclicInvocation
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

/**
 * If the type of a variable is declared with this name, the base type will be inferred from the initializer.
 */
private const val DECLARATION_TYPE_NAME_INFER = "_"

/**
 * Describes the presence/availability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class BoundVariable(
    override val context: ExecutionScopedCTContext,
    override val declaration: VariableDeclaration,
    val initializerExpression: BoundExpression<*>?,
    val kind: Kind,
) : BoundStatement<VariableDeclaration> {
    val name: String = declaration.name.value
    private val isGlobal = context is SourceFileRootContext

    val isReAssignable: Boolean = declaration.isReAssignable
    private val implicitMutability: TypeMutability = if (isReAssignable) TypeMutability.MUTABLE else kind.implicitMutabilityWhenNotReAssignable
    private val shouldInferBaseType: Boolean = declaration.type == null || declaration.type.simpleName == DECLARATION_TYPE_NAME_INFER

    /**
     * The base type reference; null if not determined yet or if it cannot be determined due to semantic errors.
     */
    var type: BoundTypeReference? = null
        private set

    private var resolvedDeclaredType: BoundTypeReference? = null

    override val isGuaranteedToThrow: Boolean?
        get() = initializerExpression?.isGuaranteedToThrow

    override val isGuaranteedToReturn: Boolean?
        get() = initializerExpression?.isGuaranteedToReturn

    private val onceAction = OnceAction()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

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

            if (declaration.initializerExpression == null && shouldInferBaseType) {
                reportings.add(
                    Reporting.typeDeductionError(
                        "Cannot determine type of $kind $name; neither type nor initializer is specified.",
                        declaration.declaredAt
                    )
                )
            }

            declaration.type
                ?.takeUnless { shouldInferBaseType }
                ?.let(context::resolveType)
                ?.defaultMutabilityTo(implicitMutability)
                ?.let { resolvedDeclaredType ->
                    this.resolvedDeclaredType = resolvedDeclaredType
                    this.type = resolvedDeclaredType
                }

            initializerExpression?.setExpectedEvaluationResultType(
                this.resolvedDeclaredType ?: BuiltinAny.baseReference
                    .withCombinedNullability(declaration.type?.nullability ?: TypeReference.Nullability.NULLABLE)
                    .withMutability(declaration.type?.mutability ?: implicitMutability)
            )

            if (shouldInferBaseType && declaration.type?.arguments?.isNotEmpty() == true) {
                reportings.add(Reporting.explicitInferTypeWithArguments(declaration.type))
            }

            if (declaration.type != null && shouldInferBaseType && !kind.allowsExplicitBaseTypeInfer) {
                reportings.add(Reporting.explicitInferTypeNotAllowed(declaration.type))
            }

            if (initializerExpression != null) {
                reportings.addAll(initializerExpression.semanticAnalysisPhase1())
            }

            return@getResult reportings
        }
    }

    override val implicitEvaluationResultType: BoundTypeReference? = null
    private var implicitEvaluationRequired = false
    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {
        implicitEvaluationRequired = true
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        initializerExpression?.setExpectedReturnType(type)
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = mutableSetOf<Reporting>()

            if (implicitEvaluationRequired) {
                reportings.add(Reporting.implicitlyEvaluatingAStatement(this))
            }

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

                if (declaration.type == null) {
                    // full inference
                    type = initializerExpression.type
                } else {
                    val finalNullability = declaration.type.nullability
                    val finalMutability = declaration.type.mutability ?: initializerExpression.type?.mutability ?: implicitMutability
                    type = resolvedDeclaredType
                        .takeUnless { shouldInferBaseType }
                        ?: BuiltinAny.baseReference
                    type = type!!
                        .withMutability(finalMutability)
                        .withCombinedNullability(finalNullability)

                    initializerExpression.type?.let { initializerType ->
                        // discrepancy between assign expression and declared type
                        if (initializerType !is UnresolvedType) {
                            initializerType.evaluateAssignabilityTo(
                                type!!,
                                declaration.initializerExpression!!.sourceLocation
                            )
                                ?.let(reportings::add)
                        }
                    }
                }
            }

            // handle no initializer case
            if (type == null) {
                type = resolvedDeclaredType
            }

            if (resolvedDeclaredType != null) {
                val useSite = kind.getTypeUseSite(declaration.sourceLocation)
                resolvedDeclaredType!!.validate(useSite).let(reportings::addAll)
            }

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            initializerExpression?.semanticAnalysisPhase3() ?: emptySet()
        }
    }

    override val modifiedContext: ExecutionScopedCTContext by lazy {
        val newCtx = MutableExecutionScopedCTContext.deriveFrom(context)
        newCtx.addVariable(this)
        if (initializerExpression != null) {
            newCtx.markVariableInitialized(this)
            newCtx.addDeferredCode(DropLocalVariableStatement(this))
        }
        newCtx
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return initializerExpression?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return initializerExpression?.findWritesBeyond(boundary) ?: emptySet()
    }

    fun isInitializedInContext(context: ExecutionScopedCTContext): Boolean {
        return isGlobal || kind == Kind.PARAMETER || context.initializesVariable(this)
    }

    val backendIrDeclaration: IrVariableDeclaration by lazy { IrVariableDeclarationImpl(name, type!!.toBackendIr()) }

    override fun toBackendIrStatement(): IrExecutable {
        if (initializerExpression == null) {
            return backendIrDeclaration
        }

        val initialTemporary = IrCreateTemporaryValueImpl(initializerExpression.toBackendIrExpression())
        val initialTemporaryRefIncrement = IrCreateReferenceStatementImpl(initialTemporary).takeUnless { initializerExpression.isEvaluationResultReferenceCounted }
        return IrCodeChunkImpl(listOfNotNull(
            backendIrDeclaration,
            initialTemporary,
            initialTemporaryRefIncrement,
            IrAssignmentStatementImpl(
                IrAssignmentStatementTargetVariableImpl(backendIrDeclaration),
                IrTemporaryValueReferenceImpl(initialTemporary),
            )
        ))
    }

    enum class Kind(
        val implicitMutabilityWhenNotReAssignable: TypeMutability,
        val allowsExplicitBaseTypeInfer: Boolean,
    ) {
        VARIABLE(TypeMutability.IMMUTABLE, true),
        PARAMETER(TypeMutability.READONLY, false),
        ;

        override fun toString() = name.lowercase()
        fun getTypeUseSite(location: SourceLocation): TypeUseSite = when (this) {
            VARIABLE -> TypeUseSite.Irrelevant
            PARAMETER -> TypeUseSite.InUsage(location)
        }
    }
}

private class IrVariableDeclarationImpl(
    override val name: String,
    override val type: IrType,
) : IrVariableDeclaration