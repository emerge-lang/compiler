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
import compiler.binding.type.ErroneousType
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.circularVariableInitialization
import compiler.diagnostic.explicitInferTypeNotAllowed
import compiler.diagnostic.explicitInferTypeWithArguments
import compiler.diagnostic.explicitOwnershipNotAllowed
import compiler.diagnostic.globalVariableNotInitialized
import compiler.diagnostic.quoteIdentifier
import compiler.diagnostic.typeDeductionError
import compiler.diagnostic.variableDeclaredMoreThanOnce
import compiler.diagnostic.variableTypeNotDeclared
import compiler.diagnostic.visibilityNotAllowedOnVariable
import compiler.handleCyclicInvocation
import compiler.lexer.Span
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
    private val typeInferenceStrategy: TypeInferenceStrategy,
    val kind: Kind,
) : BoundStatement<VariableDeclaration>, DefinitionWithVisibility {
    private val seanHelper = SeanHelper()

    val name: String = declaration.name.value
    private val isGlobal = kind == Kind.GLOBAL_VARIABLE

    val isReAssignable: Boolean = declaration.isReAssignable

    var typeInferenceStage2: TypeInferenceStrategy.Sean2Stage by seanHelper.resultOfPhase1(allowReassignment = false)
    var typeInferenceStage3: TypeInferenceStrategy.Sean3Stage by seanHelper.resultOfPhase2(allowReassignment = false)

    /**
     * The type as _declared_ or inferred _from the declaration only_; there is some level of dependent typing
     * (e.g. null checks, instanceof-checks) that can narrow the type of variables. Use [getTypeInContext] to obtain
     * the correct type.
     *
     * null if not determined yet or if it cannot be determined due to semantic errors.
     * Available after [semanticAnalysisPhase2]; iff a type is declared and no inference is needed,
     * already available after [semanticAnalysisPhase1].
     */
    val typeAtDeclarationTime: BoundTypeReference?
        get() = when {
            seanHelper.phase2Done -> typeInferenceStage3.typeAfterSean2
            seanHelper.phase1Done -> typeInferenceStage2.typeAfterSean1
            else -> null
        }

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

    private var hasCircularInitialization: Boolean by seanHelper.resultOfPhase1(allowReassignment = false)

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            visibility.semanticAnalysisPhase1(diagnosis)
            if (!kind.allowsVisibility && declaration.visibility != null) {
                diagnosis.visibilityNotAllowedOnVariable(this)
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

            typeInferenceStage2 = typeInferenceStrategy.init(
                context,
                kind,
                isReAssignable,
                name,
                declaration.span,
            ).doSean1(declaration.type, initializerExpression != null, diagnosis)

            if (initializerExpression != null) {
                handleCyclicInvocation(
                    context = this,
                    action = {
                        initializerExpression.semanticAnalysisPhase1(diagnosis)
                        hasCircularInitialization = false
                    },
                    onCycle = {
                        diagnosis.circularVariableInitialization(this)
                        hasCircularInitialization = true
                    },
                )
                typeInferenceStage2.expectedInitializerEvaluationType?.let {
                    initializerExpression.setExpectedEvaluationResultType(it, diagnosis)
                }
                initializerExpression.markEvaluationResultUsed()
            } else {
                hasCircularInitialization = false
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
                if (!hasCircularInitialization) {
                    initializerExpression.semanticAnalysisPhase2(diagnosis)
                }
                typeInferenceStage3 = typeInferenceStage2.doSean2WithInitializer(initializerExpression, diagnosis)

                initializerExpression.setEvaluationResultUsage(CreateReferenceValueUsage(
                    typeInferenceStage3.typeAfterSean2,
                    declaration.declaredAt,
                    ownershipAtDeclarationTime,
                ))
            } else {
                typeInferenceStage3 = typeInferenceStage2.doSean2WithoutInitializer(diagnosis)
            }

            if (declaration.type != null && typeInferenceStage2.typeAfterSean1 != null) {
                val useSite = kind.getTypeUseSite(this, declaration.span)
                typeInferenceStage2.typeAfterSean1!!.validate(useSite, diagnosis)
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
            newCtx.addDeferredCode(DeferredLocalVariableGCRelease(this))
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

    override fun toStringForErrorMessage() = "$kind ${name.quoteIdentifier()}"

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
        val allowsExplicitOwnership: Boolean,
        val isInitializedByDefault: Boolean,
        val allowsVisibility: Boolean,
        val runInitializerInSubScope: Boolean,
        val allowsShadowingGlobals: Boolean = false,
    ) {
        LOCAL_VARIABLE(
            "local variable",
            implicitMutabilityWhenNotReAssignable = TypeMutability.IMMUTABLE,
            allowsExplicitOwnership = false,
            isInitializedByDefault = false,
            allowsVisibility = false,
            runInitializerInSubScope = false,
        ),
        MEMBER_VARIABLE(
            "member variable",
            implicitMutabilityWhenNotReAssignable = TypeMutability.IMMUTABLE,
            allowsExplicitOwnership = false,
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
            implicitMutabilityWhenNotReAssignable = TypeMutability.READONLY,
            allowsExplicitOwnership = MEMBER_VARIABLE.allowsExplicitOwnership,
            isInitializedByDefault = MEMBER_VARIABLE.isInitializedByDefault,
            allowsVisibility = MEMBER_VARIABLE.allowsVisibility,
            runInitializerInSubScope = MEMBER_VARIABLE.runInitializerInSubScope,
            allowsShadowingGlobals = MEMBER_VARIABLE.allowsShadowingGlobals,
        ),
        GLOBAL_VARIABLE(
            readableKindName = "global variable",
            implicitMutabilityWhenNotReAssignable = TypeMutability.IMMUTABLE,
            allowsExplicitOwnership = false,
            isInitializedByDefault = true,
            allowsVisibility = true,
            runInitializerInSubScope = true,
        ),
        PARAMETER(
            readableKindName = "parameter",
            implicitMutabilityWhenNotReAssignable = TypeMutability.READONLY,
            allowsExplicitOwnership = true,
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
            PARAMETER.allowsExplicitOwnership,
            PARAMETER.isInitializedByDefault,
            PARAMETER.allowsVisibility,
            PARAMETER.runInitializerInSubScope,
            /* see the reasoning for allowShadowingGlobals on member variables;
               this is because constructor parameters are named like the class members they take init values for.
             */
            allowsShadowingGlobals = true,
        )
        ;

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

    /**
     * Decouples type inference logic from the other semantic analysis that goes on around variables for simplicity.
     */
    interface TypeInferenceStrategy {
        private companion object {
            val TypeReference.requestsBaseTypeInference: Boolean
                get() = this is NamedTypeReference && simpleName == BoundTypeReference.NAME_REQUESTING_TYPE_INFERENCE
        }

        fun init(
            context: CTContext,
            kind: Kind,
            isReAssignable: Boolean,
            name: String,
            declaredAt: Span
        ): Sean1Stage

        interface Sean1Stage {
            fun doSean1(declaredType: TypeReference?, hasInitializer: Boolean, diagnosis: Diagnosis): Sean2Stage
        }

        interface Sean2Stage {
            val typeAfterSean1: BoundTypeReference?
            val expectedInitializerEvaluationType: BoundTypeReference?
            val utilizesInitializerType: Boolean

            fun doSean2WithInitializer(initializerExpression: BoundExpression<*>, diagnosis: Diagnosis): Sean3Stage
            fun doSean2WithoutInitializer(diagnosis: Diagnosis): Sean3Stage
        }

        interface Sean3Stage {
            val typeAfterSean2: BoundTypeReference?
        }

        /**
         * No inference, the type must be declared explicitly. For function parameters that are not a receiver with implied type.
         */
        object NoInference : TypeInferenceStrategy {
            override fun init(
                context: CTContext,
                kind: Kind,
                isReAssignable: Boolean,
                name: String,
                declaredAt: Span
            ): Sean1Stage = object : Sean1Stage {
                override fun doSean1(declaredType: TypeReference?, hasInitializer: Boolean, diagnosis: Diagnosis): Sean2Stage {
                    return object : Sean2Stage {
                        override val utilizesInitializerType = false
                        override val typeAfterSean1: BoundTypeReference? =
                            if (declaredType != null) {
                                if (declaredType.requestsBaseTypeInference) {
                                    diagnosis.explicitInferTypeNotAllowed(declaredType)
                                    null
                                } else {
                                    context.resolveType(declaredType)
                                }
                            } else {
                                diagnosis.variableTypeNotDeclared(kind, name, declaredAt)
                                null
                            }

                        override val expectedInitializerEvaluationType: BoundTypeReference
                            get() =  context.swCtx.any.getBoundReferenceAssertNoTypeParameters(declaredAt)
                                .withCombinedNullability(declaredType?.nullability ?: TypeReference.Nullability.NULLABLE)
                                .withMutability(declaredType?.mutability ?: TypeMutability.READONLY)

                        override fun doSean2WithInitializer(
                            initializerExpression: BoundExpression<*>,
                            diagnosis: Diagnosis
                        ): Sean3Stage {
                            return doSean2WithoutInitializer(diagnosis)
                        }

                        override fun doSean2WithoutInitializer(diagnosis: Diagnosis): Sean3Stage {
                            return object : Sean3Stage {
                                override val typeAfterSean2 = typeAfterSean1
                            }
                        }
                    }
                }
            }
        }

        /**
         * Mutability is inferred from [BoundVariable.isReAssignable] and when the basetype simplename of the
         * declared type is [BoundTypeReference.NAME_REQUESTING_TYPE_INFERENCE], the base type is inferred from
         * the initializer expression.
         */
        object InferBaseTypeAndMutability : TypeInferenceStrategy {
            override fun init(
                context: CTContext,
                kind: Kind,
                isReAssignable: Boolean,
                name: String,
                declaredAt: Span,
            ): Sean1Stage = object : Sean1Stage {
                private val implicitMutability: TypeMutability = if (isReAssignable) TypeMutability.MUTABLE else kind.implicitMutabilityWhenNotReAssignable

                override fun doSean1(declaredType: TypeReference?, hasInitializer: Boolean, diagnosis: Diagnosis): Sean2Stage {
                    val shouldInferBaseType = when {
                        declaredType == null -> true
                        declaredType.requestsBaseTypeInference -> {
                            declaredType as NamedTypeReference
                            if (declaredType.arguments?.isNotEmpty() == true) {
                                diagnosis.explicitInferTypeWithArguments(declaredType)
                            }
                            true
                        }
                        else -> false
                    }

                    if (shouldInferBaseType && !hasInitializer) {
                        diagnosis.typeDeductionError(
                            "Cannot determine type of ${kind.readableKindName} $name; neither type nor initializer is specified.",
                            declaredAt,
                        )
                    }

                    return object : Sean2Stage {
                        override val utilizesInitializerType = shouldInferBaseType
                        override val typeAfterSean1: BoundTypeReference? = declaredType
                            ?.takeUnless { shouldInferBaseType }
                            ?.let(context::resolveType)
                            ?.defaultMutabilityTo(implicitMutability)

                        override val expectedInitializerEvaluationType: BoundTypeReference?
                            get() = when {
                                typeAfterSean1 != null -> typeAfterSean1
                                declaredType != null -> context.swCtx.any.getBoundReferenceAssertNoTypeParameters(declaredAt)
                                    .withCombinedNullability(declaredType.nullability)
                                    .withMutability(declaredType.mutability ?: implicitMutability)
                                else -> null
                            }

                        override fun doSean2WithInitializer(
                            initializerExpression: BoundExpression<*>,
                            diagnosis: Diagnosis
                        ): Sean3Stage {
                            var typeAfterSean2: BoundTypeReference?
                            if (declaredType == null) {
                                // full inference
                                typeAfterSean2 = initializerExpression.type?.withMutabilityUnionedWith(implicitMutability)
                            } else {
                                val finalNullability = declaredType.nullability
                                val finalMutability = declaredType.mutability
                                    ?: if (initializerExpression.type?.mutability?.isAssignableTo(implicitMutability) != false) implicitMutability else TypeMutability.READONLY

                                if (shouldInferBaseType) {
                                    typeAfterSean2 = initializerExpression.type
                                } else {
                                    typeAfterSean2 = typeAfterSean1
                                }

                                typeAfterSean2 = typeAfterSean2
                                    ?.withMutability(finalMutability)
                                    ?.withCombinedNullability(finalNullability)

                                initializerExpression.type?.let { initializerType ->
                                    // discrepancy between assign expression and declared type
                                    if (initializerType !is ErroneousType) {
                                        initializerType.evaluateAssignabilityTo(
                                            typeAfterSean2!!,
                                            initializerExpression.declaration.span,
                                        )
                                            ?.let(diagnosis::add)
                                    }
                                }
                            }

                            return object : Sean3Stage {
                                override val typeAfterSean2: BoundTypeReference? = typeAfterSean2
                            }
                        }

                        override fun doSean2WithoutInitializer(diagnosis: Diagnosis): Sean3Stage {
                            return object : Sean3Stage {
                                override val typeAfterSean2: BoundTypeReference? = typeAfterSean1
                            }
                        }
                    }
                }
            }
        }

        class ImpliedTypeIgnoreInitializer(
            val lazyGetImpliedType: () -> RootResolvedTypeReference
        ) : TypeInferenceStrategy {
            override fun init(
                context: CTContext,
                kind: Kind,
                isReAssignable: Boolean,
                name: String,
                declaredAt: Span,
            ): Sean1Stage {
                return object : Sean1Stage {
                    override fun doSean1(declaredType: TypeReference?, hasInitializer: Boolean, diagnosis: Diagnosis): Sean2Stage {
                        val impliedType = lazyGetImpliedType()
                        return object : Sean2Stage {
                            override val utilizesInitializerType = false
                            override val typeAfterSean1 =
                                declaredType
                                    ?.resolveWithImpliedType(impliedType, context)
                                    ?: impliedType

                            override val expectedInitializerEvaluationType: BoundTypeReference = typeAfterSean1

                            override fun doSean2WithInitializer(
                                initializerExpression: BoundExpression<*>,
                                diagnosis: Diagnosis
                            ): Sean3Stage {
                                return doSean2WithoutInitializer(diagnosis)
                            }

                            override fun doSean2WithoutInitializer(diagnosis: Diagnosis): Sean3Stage {
                                return object : Sean3Stage {
                                    override val typeAfterSean2 = typeAfterSean1
                                }
                            }
                        }
                    }
                }
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