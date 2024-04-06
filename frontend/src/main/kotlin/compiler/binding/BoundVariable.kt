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
import compiler.OnceAction
import compiler.ast.VariableDeclaration
import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.VariableInitialization
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
 * Describes the presence/availability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class BoundVariable(
    override val context: ExecutionScopedCTContext,
    override val declaration: VariableDeclaration,
    override val visibility: BoundVisibility,
    val initializerExpression: BoundExpression<*>?,
    val kind: Kind,
) : BoundStatement<VariableDeclaration>, DefinitionWithVisibility {
    val name: String = declaration.name.value
    private val isGlobal = kind == Kind.GLOBAL_VARIABLE

    val isReAssignable: Boolean = declaration.isReAssignable
    private val implicitMutability: TypeMutability = if (isReAssignable) TypeMutability.MUTABLE else kind.implicitMutabilityWhenNotReAssignable
    private val shouldInferBaseType: Boolean = declaration.type == null || declaration.type.simpleName == DECLARATION_TYPE_NAME_INFER

    /**
     * The type as _declared_ or inferred _from the declaration only_; there is some level of dependent typing
     * (e.g. null checks, instanceof-checks) that can narrow the type of variables. Use [getTypeInContext] to obtain
     * the correct type.
     *
     * null if not determined yet or if it cannot be determined due to semantic errors.
     */
    var typeAtDeclarationTime: BoundTypeReference? = null
        private set

    /**
     * The type, solely as _declared_ (excluding type inference). Null if fully inferred or not resolved yet
     */
    private var resolvedDeclaredType: BoundTypeReference? = null
    private val expectedInitializerEvaluationType: BoundTypeReference
        get() = this.resolvedDeclaredType ?: BuiltinAny.baseReference
            .withCombinedNullability(declaration.type?.nullability ?: TypeReference.Nullability.NULLABLE)
            .withMutability(declaration.type?.mutability ?: implicitMutability)

    /**
     * publicly mutable so that it can be changed depending on context. However, the value must be set before
     * [semanticAnalysisPhase1]
     */
    var defaultOwnership: VariableOwnership = VariableOwnership.CAPTURED
        set(value) {
            onceAction.requireActionNotDone(OnceAction.SemanticAnalysisPhase1)
            field = value
        }

    /**
     * The ownership as declared, or [defaultOwnership]
     */
    val ownershipAtDeclarationTime: VariableOwnership
        get() = declaration.ownership?.first?.takeIf { kind.allowsExplicitOwnership }
            ?: defaultOwnership

    override val isGuaranteedToThrow: Boolean?
        get() = initializerExpression?.isGuaranteedToThrow

    override val isGuaranteedToReturn: Boolean?
        get() = initializerExpression?.isGuaranteedToReturn

    private val onceAction = OnceAction()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            reportings.addAll(visibility.semanticAnalysisPhase1())
            if (!kind.allowsVisibility && declaration.visibility != null) {
                reportings.add(Reporting.visibilityNotAllowedOnVariable(this))
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

            if (kind.requiresExplicitType) {
                if (declaration.type == null) {
                    reportings.add(Reporting.variableTypeNotDeclared(this))
                }
            } else if (declaration.initializerExpression == null && shouldInferBaseType) {
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
                    this.typeAtDeclarationTime = resolvedDeclaredType
                }

            initializerExpression?.setExpectedEvaluationResultType(expectedInitializerEvaluationType)

            if (shouldInferBaseType && declaration.type?.arguments?.isNotEmpty() == true) {
                reportings.add(Reporting.explicitInferTypeWithArguments(declaration.type))
            }

            if (declaration.type != null && shouldInferBaseType && !kind.allowsExplicitBaseTypeInfer) {
                reportings.add(Reporting.explicitInferTypeNotAllowed(declaration.type))
            }

            if (declaration.ownership != null && !kind.allowsExplicitOwnership) {
                reportings.add(Reporting.explicitOwnershipNotAllowed(this))
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

            reportings.addAll(visibility.semanticAnalysisPhase2())

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
                    typeAtDeclarationTime = initializerExpression.type?.withCombinedMutability(implicitMutability)
                } else {
                    val finalNullability = declaration.type.nullability
                    val finalMutability = declaration.type.mutability
                        ?: if (initializerExpression.type?.mutability?.isAssignableTo(implicitMutability) != false) implicitMutability else TypeMutability.READONLY

                    if (shouldInferBaseType) {
                        typeAtDeclarationTime = initializerExpression.type
                    } else {
                        typeAtDeclarationTime = resolvedDeclaredType
                    }

                    typeAtDeclarationTime = typeAtDeclarationTime!!
                        .withMutability(finalMutability)
                        .withCombinedNullability(finalNullability)

                    initializerExpression.type?.let { initializerType ->
                        // discrepancy between assign expression and declared type
                        if (initializerType !is UnresolvedType) {
                            initializerType.evaluateAssignabilityTo(
                                typeAtDeclarationTime!!,
                                declaration.initializerExpression!!.sourceLocation
                            )
                                ?.let(reportings::add)
                        }
                    }
                }
            }

            // handle no initializer case
            if (typeAtDeclarationTime == null) {
                typeAtDeclarationTime = resolvedDeclaredType
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
            initializerExpression?.markEvaluationResultCaptured(typeAtDeclarationTime?.mutability ?: implicitMutability)
            val reportings = mutableListOf<Reporting>()

            initializerExpression?.semanticAnalysisPhase3()?.let(reportings::addAll)
            reportings.addAll(visibility.semanticAnalysisPhase3())

            reportings
        }
    }

    override val modifiedContext: ExecutionScopedCTContext by lazy {
        val contextAfterInitializer = initializerExpression?.modifiedContext ?: context
        val newCtx = MutableExecutionScopedCTContext.deriveFrom(contextAfterInitializer)
        newCtx.addVariable(this)
        if (initializerExpression != null) {
            newCtx.trackSideEffect(VariableInitialization.WriteToVariableEffect(this))
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

    fun getInitializationStateInContext(context: ExecutionScopedCTContext): VariableInitialization.State {
        if (kind.isInitializedByDefault) {
            return VariableInitialization.State.INITIALIZED
        }

        return context.getEphemeralState(VariableInitialization, this)
    }

    /**
     * @return the type of this variable in this specific context. Used to implement additional type inference,
     * e.g. instanceof checks, null checks, partial initialization, ...
     */
    fun getTypeInContext(context: ExecutionScopedCTContext): BoundTypeReference? {
        // TODO: usage of this was refactored away, but it may become useful again for smart casts -> implement them here
        return typeAtDeclarationTime
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        if (!kind.allowsVisibility) {
            throw InternalCompilerError("A $kind does not have visibility, cannot validate access")
        }

        return visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "$kind $name"

    val backendIrDeclaration: IrVariableDeclaration by lazy { IrVariableDeclarationImpl(name, typeAtDeclarationTime!!.toBackendIr()) }

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
        val allowsExplicitOwnership: Boolean,
        val requiresExplicitType: Boolean,
        val isInitializedByDefault: Boolean,
        val allowsVisibility: Boolean,
    ) {
        LOCAL_VARIABLE(
            implicitMutabilityWhenNotReAssignable = TypeMutability.IMMUTABLE,
            allowsExplicitBaseTypeInfer = true,
            allowsExplicitOwnership = false,
            requiresExplicitType = false,
            isInitializedByDefault = false,
            allowsVisibility = false,
        ),
        MEMBER_VARIABLE(
            TypeMutability.IMMUTABLE,
            allowsExplicitBaseTypeInfer = true,
            allowsExplicitOwnership = false,
            requiresExplicitType = false,
            isInitializedByDefault = false,
            allowsVisibility = true,
        ),
        GLOBAL_VARIABLE(
            TypeMutability.IMMUTABLE,
            allowsExplicitBaseTypeInfer = true,
            allowsExplicitOwnership = false,
            requiresExplicitType = false,
            isInitializedByDefault = true,
            allowsVisibility = true,
        ),
        PARAMETER(
            TypeMutability.READONLY,
            allowsExplicitBaseTypeInfer = false,
            allowsExplicitOwnership = true,
            requiresExplicitType = true,
            isInitializedByDefault = true,
            allowsVisibility = false,
        ),
        ;

        init {
            if (requiresExplicitType) {
                check(!allowsExplicitBaseTypeInfer)
            }
        }

        override fun toString() = name.lowercase().replace('_', ' ')
        fun getTypeUseSite(location: SourceLocation): TypeUseSite = when (this) {
            LOCAL_VARIABLE,
            MEMBER_VARIABLE,
            GLOBAL_VARIABLE -> TypeUseSite.Irrelevant(location)
            PARAMETER -> TypeUseSite.InUsage(location)
        }
    }

    companion object {
        /**
         * If the type of a variable is declared with this name, the base type will be inferred from the initializer.
         */
        const val DECLARATION_TYPE_NAME_INFER = "_"
    }
}

private class IrVariableDeclarationImpl(
    override val name: String,
    override val type: IrType,
) : IrVariableDeclaration