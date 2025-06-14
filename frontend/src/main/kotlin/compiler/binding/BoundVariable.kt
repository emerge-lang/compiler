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
import compiler.ast.VariableDeclaration
import compiler.ast.VariableOwnership
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.CreateReferenceValueUsage
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.explicitInferTypeNotAllowed
import compiler.diagnostic.explicitInferTypeWithArguments
import compiler.diagnostic.explicitOwnershipNotAllowed
import compiler.diagnostic.globalVariableNotInitialized
import compiler.diagnostic.typeDeductionError
import compiler.diagnostic.variableDeclaredMoreThanOnce
import compiler.diagnostic.variableTypeNotDeclared
import compiler.diagnostic.visibilityNotAllowedOnVariable
import compiler.handleCyclicInvocation
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import kotlin.properties.Delegates.notNull

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
    /** initialized during [semanticAnalysisPhase1] */
    private var shouldInferBaseType: Boolean by notNull()

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
        get() = this.resolvedDeclaredType
            ?: context.swCtx.any.baseReference
                .withCombinedNullability(declaration.type?.nullability ?: TypeReference.Nullability.NULLABLE)
                .withMutability(declaration.type?.mutability ?: implicitMutability)

    /**
     * publicly mutable so that it can be changed depending on context. However, the value must be set before
     * [semanticAnalysisPhase1]
     */
    var defaultOwnership: VariableOwnership = VariableOwnership.CAPTURED
        set(value) {
            seanHelper.requirePhase1NotDone()
            field = value
        }

    /**
     * The ownership as declared, or [defaultOwnership]
     */
    val ownershipAtDeclarationTime: VariableOwnership
        get() = declaration.ownership?.first?.takeIf { kind.allowsExplicitOwnership }
            ?: defaultOwnership

    override val returnBehavior get() = if (initializerExpression == null) SideEffectPrediction.NEVER else initializerExpression.returnBehavior
    override val throwBehavior get() = if (initializerExpression == null) SideEffectPrediction.NEVER else initializerExpression.throwBehavior

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            visibility.semanticAnalysisPhase1(diagnosis)
            if (!kind.allowsVisibility && declaration.visibility != null) {
                diagnosis.visibilityNotAllowedOnVariable(this)
            }

            shouldInferBaseType = when (declaration.type) {
                null -> true
                is NamedTypeReference -> when (declaration.type.simpleName) {
                    BoundTypeReference.NAME_REQUESTING_TYPE_INFERENCE -> {
                        if (declaration.type.arguments?.isNotEmpty() == true) {
                            diagnosis.explicitInferTypeWithArguments(declaration.type)
                        }
                        true
                    }
                    else -> false
                }
                else -> false
            }

            context.resolveVariable(this.name)
                ?.takeUnless { it === this }
                ?.takeUnless { shadowed -> this.kind.allowsShadowingGlobals && shadowed.isGlobal }
                ?.let { firstDeclarationOfVariable ->
                    diagnosis.variableDeclaredMoreThanOnce(
                        firstDeclarationOfVariable.declaration,
                        this.declaration
                    )
                }

            if (isGlobal && declaration.initializerExpression == null) {
                diagnosis.globalVariableNotInitialized(this)
            }

            if (kind.requiresExplicitType) {
                if (declaration.type == null) {
                    diagnosis.variableTypeNotDeclared(this)
                }
            } else if (declaration.initializerExpression == null && shouldInferBaseType) {
                diagnosis.typeDeductionError(
                    "Cannot determine type of $kind $name; neither type nor initializer is specified.",
                    declaration.declaredAt
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

            if (initializerExpression != null) {
                initializerExpression.semanticAnalysisPhase1(diagnosis)
                initializerExpression.setExpectedEvaluationResultType(expectedInitializerEvaluationType, diagnosis)
                initializerExpression.markEvaluationResultUsed()
            }

            if (declaration.type != null && shouldInferBaseType && !kind.allowsExplicitBaseTypeInfer) {
                diagnosis.explicitInferTypeNotAllowed(declaration.type)
            }

            if (declaration.ownership != null && !kind.allowsExplicitOwnership) {
                diagnosis.explicitOwnershipNotAllowed(this)
            }
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        initializerExpression?.setExpectedReturnType(type, diagnosis)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {

            visibility.semanticAnalysisPhase2(diagnosis)

            if (initializerExpression != null) {
                handleCyclicInvocation(
                    context = this,
                    action = {
                        initializerExpression.semanticAnalysisPhase2(diagnosis)
                    },
                    onCycle = {
                        diagnosis.typeDeductionError(
                            "Cannot infer the type of variable $name because the type inference is cyclic here. Specify the type of one element explicitly.",
                            initializerExpression.declaration.span
                        )
                    },
                )

                if (declaration.type == null) {
                    // full inference
                    typeAtDeclarationTime = initializerExpression.type?.withMutabilityIntersectedWith(implicitMutability)
                } else {
                    val finalNullability = declaration.type.nullability
                    val finalMutability = declaration.type.mutability
                        ?: if (initializerExpression.type?.mutability?.isAssignableTo(implicitMutability) != false) implicitMutability else TypeMutability.READONLY

                    if (shouldInferBaseType) {
                        typeAtDeclarationTime = initializerExpression.type
                    } else {
                        typeAtDeclarationTime = resolvedDeclaredType
                    }

                    typeAtDeclarationTime = typeAtDeclarationTime
                        ?.withMutability(finalMutability)
                        ?.withCombinedNullability(finalNullability)

                    initializerExpression.type?.let { initializerType ->
                        // discrepancy between assign expression and declared type
                        if (initializerType !is UnresolvedType) {
                            initializerType.evaluateAssignabilityTo(
                                typeAtDeclarationTime!!,
                                declaration.initializerExpression!!.span
                            )
                                ?.let(diagnosis::add)
                        }
                    }
                }

                initializerExpression.setEvaluationResultUsage(CreateReferenceValueUsage(
                    typeAtDeclarationTime,
                    declaration.declaredAt,
                    ownershipAtDeclarationTime,
                ))
            }

            // handle no initializer case
            if (typeAtDeclarationTime == null) {
                typeAtDeclarationTime = resolvedDeclaredType
            }

            if (resolvedDeclaredType != null) {
                val useSite = kind.getTypeUseSite(this, declaration.span)
                resolvedDeclaredType!!.validate(useSite, diagnosis)
            }
        }
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        initializerExpression?.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            initializerExpression?.semanticAnalysisPhase3(diagnosis)
            visibility.semanticAnalysisPhase3(diagnosis)
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

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        initializerExpression?.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        initializerExpression?.visitWritesBeyond(boundary, visitor)
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

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        if (!kind.allowsVisibility) {
            throw InternalCompilerError("A $kind does not have visibility, cannot validate access")
        }

        return visibility.validateAccessFrom(location, this, diagnosis)
    }

    override fun toStringForErrorMessage() = "$kind $name"

    val backendIrDeclaration: IrVariableDeclaration by lazy {
        val isSSA = when  {
            isReAssignable -> false
            initializerExpression != null -> true
            else -> {
                // there are some special variables, e.g. self within constructors, that don't get an initializerExpression
                // but are nonetheless immediately initialized by otherwise generated IR, e.g. IrAllocateObjectExpression
                // marking these as ínitialized is important for semantic validation to pass, making that a pretty
                // reliable source of information
                val isExternallyInitialized = context.getEphemeralState(VariableInitialization, this) == VariableInitialization.State.INITIALIZED
                isExternallyInitialized
            }
        }
        IrVariableDeclarationImpl(
            name,
            typeAtDeclarationTime!!.toBackendIr(),
            isBorrowed = ownershipAtDeclarationTime == VariableOwnership.BORROWED,
            isReAssignable = isReAssignable,
            isSSA = isSSA,
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        if (initializerExpression == null) {
            return backendIrDeclaration
        }

        val initialTemporary = IrCreateTemporaryValueImpl(initializerExpression.toBackendIrExpression())
        val initialTemporaryRefIncrement = IrCreateStrongReferenceStatementImpl(initialTemporary).takeUnless { initializerExpression.isEvaluationResultReferenceCounted }
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

    override fun toString(): String {
        return "${ownershipAtDeclarationTime.keyword.text} $name: ${typeAtDeclarationTime ?: "?"}; ${declaration.declaredAt.sourceFile.name} line ${declaration.declaredAt.fromLineNumber}"
    }

    enum class Kind(
        val readableKindName: String,
        val implicitMutabilityWhenNotReAssignable: TypeMutability,
        val allowsExplicitBaseTypeInfer: Boolean,
        val allowsExplicitOwnership: Boolean,
        val requiresExplicitType: Boolean,
        val isInitializedByDefault: Boolean,
        val allowsVisibility: Boolean,
        val runInitializerInSubScope: Boolean,
        val allowsShadowingGlobals: Boolean = false,
    ) {
        LOCAL_VARIABLE(
            "local variable",
            implicitMutabilityWhenNotReAssignable = TypeMutability.IMMUTABLE,
            allowsExplicitBaseTypeInfer = true,
            allowsExplicitOwnership = false,
            requiresExplicitType = false,
            isInitializedByDefault = false,
            allowsVisibility = false,
            runInitializerInSubScope = false,
        ),
        MEMBER_VARIABLE(
            "member variable",
            TypeMutability.IMMUTABLE,
            allowsExplicitBaseTypeInfer = true,
            allowsExplicitOwnership = false,
            requiresExplicitType = false,
            isInitializedByDefault = false,
            allowsVisibility = true,
            runInitializerInSubScope = false,
            /* class members cannot be in name conflict with global variables because access to them is always
               qualified by a member-access expression, either through self or another variable name.
             */
            allowsShadowingGlobals = true,
        ),
        DECORATED_MEMBER_VARIABLE(
            readableKindName = "member variable",
            TypeMutability.READONLY,
            allowsExplicitBaseTypeInfer = MEMBER_VARIABLE.allowsExplicitBaseTypeInfer,
            allowsExplicitOwnership = MEMBER_VARIABLE.allowsExplicitOwnership,
            requiresExplicitType = MEMBER_VARIABLE.requiresExplicitType,
            isInitializedByDefault = MEMBER_VARIABLE.isInitializedByDefault,
            allowsVisibility = MEMBER_VARIABLE.allowsVisibility,
            runInitializerInSubScope = MEMBER_VARIABLE.runInitializerInSubScope,
            allowsShadowingGlobals = MEMBER_VARIABLE.allowsShadowingGlobals,
        ),
        GLOBAL_VARIABLE(
            readableKindName = "global variable",
            TypeMutability.IMMUTABLE,
            allowsExplicitBaseTypeInfer = true,
            allowsExplicitOwnership = false,
            requiresExplicitType = false,
            isInitializedByDefault = true,
            allowsVisibility = true,
            runInitializerInSubScope = true,
        ),
        PARAMETER(
            readableKindName = "parameter",
            TypeMutability.READONLY,
            allowsExplicitBaseTypeInfer = false,
            allowsExplicitOwnership = true,
            requiresExplicitType = true,
            isInitializedByDefault = true,
            allowsVisibility = false,
            runInitializerInSubScope = false,
        ),
        /**
         * By definition identical to [PARAMETER], except that [TypeVariance] of the declared type is not relevant
         * ([getTypeUseSite] returns an [TypeUseSite.Irrelevant])
         */
        CONSTRUCTOR_PARAMETER(
            readableKindName = "constructor parameter",
            PARAMETER.implicitMutabilityWhenNotReAssignable,
            PARAMETER.allowsExplicitBaseTypeInfer,
            PARAMETER.allowsExplicitOwnership,
            PARAMETER.requiresExplicitType,
            PARAMETER.isInitializedByDefault,
            PARAMETER.allowsVisibility,
            PARAMETER.runInitializerInSubScope,
            /* see the reasoning for allowShadowingGlobals on member variables;
               this is because constructor parameters are named like the class members they take init values for.
             */
            allowsShadowingGlobals = true,
        )
        ;

        init {
            if (requiresExplicitType) {
                check(!allowsExplicitBaseTypeInfer)
            }
        }

        override fun toString() = name.lowercase().replace('_', ' ')
        fun getTypeUseSite(exposedBy: DefinitionWithVisibility,  location: Span): TypeUseSite {
            val effectiveExposedBy = exposedBy.takeIf { allowsVisibility }
            return when (this) {
                LOCAL_VARIABLE,
                MEMBER_VARIABLE,
                DECORATED_MEMBER_VARIABLE,
                GLOBAL_VARIABLE,
                CONSTRUCTOR_PARAMETER -> TypeUseSite.Irrelevant(location, effectiveExposedBy)
                PARAMETER -> TypeUseSite.InUsage(location, effectiveExposedBy)
            }
        }
    }
}

private class IrVariableDeclarationImpl(
    override val name: String,
    override val type: IrType,
    override val isBorrowed: Boolean,
    override val isReAssignable: Boolean,
    override val isSSA: Boolean,
) : IrVariableDeclaration