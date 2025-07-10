package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.AssignmentStatement
import compiler.ast.AstCodeChunk
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.VariableOwnership
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.AstIntersectionType
import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundParameterList
import compiler.binding.BoundVariable
import compiler.binding.IrAssignmentStatementImpl
import compiler.binding.IrAssignmentStatementTargetClassFieldImpl
import compiler.binding.IrAssignmentStatementTargetVariableImpl
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.IrReturnStatementImpl
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.impurity.DiagnosingImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.IrSimpleTypeImpl
import compiler.diagnostic.ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.constructorDeclaredAsModifying
import compiler.diagnostic.constructorDeclaredNothrow
import compiler.diagnostic.illegalMixinRepetition
import compiler.handleCyclicInvocation
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrConstructor
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrRegisterWeakReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.independentToString
import io.github.tmarsteel.emerge.common.CanonicalElementName

/**
 * The constructor of a class that, once compiled, does the basic bootstrapping:
 * 1. accept values for the constructor-initialized member variables
 * 2. allocate memory for the new object
 * 3. initialize all member variables as appropriate / as defined in their initializer expressions
 * 4. execute user-defined code additionally defined in a `constructor { ... }` block in the class definition
 */
class BoundClassConstructor(
    override val parentContext: CTContext,
    fileContextWithTypeParametersDeclaredOnBaseType: CTContext,
    override val declaredTypeParameters: List<BoundTypeParameter>,
    val boundMemberVariables: List<BoundBaseTypeMemberVariable>,
    getClassDef: () -> BoundBaseType,
    val declaration: BaseTypeConstructorDeclaration,
) : BoundFunction, BoundBaseTypeEntry<BaseTypeConstructorDeclaration> {
    val classDef: BoundBaseType by lazy(getClassDef)
    private val generatedSourceLocation = declaration.span.deriveGenerated()
    override val canonicalName: CanonicalElementName.Function by lazy {
        CanonicalElementName.Function(classDef.canonicalName, "\$constructor")
    }

    private val fileContextWithAllTypeParameters: CTContext
    private val typeParameterForDecoratorMutability: BoundTypeParameter?
    private val additionalTypeParametersForDecoratedMembers = mutableMapOf<BoundBaseTypeMemberVariable, BoundTypeParameter>()
    init {
        val decoratedCtorInitializedMembers = boundMemberVariables.filter { it.isDecorated && it.isConstructorParameterInitialized }
        if (decoratedCtorInitializedMembers.isNotEmpty()) {
            typeParameterForDecoratorMutability = TypeParameter(
                TypeVariance.UNSPECIFIED,
                IdentifierToken(fileContextWithTypeParametersDeclaredOnBaseType.findInternalVariableName("M"), generatedSourceLocation),
                null,
            ).bindTo(fileContextWithTypeParametersDeclaredOnBaseType)
            var contextCarry = typeParameterForDecoratorMutability.modifiedContext
            val refToTypeParameterForDecoratorMutability = NamedTypeReference(IdentifierToken(typeParameterForDecoratorMutability.name, generatedSourceLocation))
            decoratedCtorInitializedMembers
                .filter { it.type == null || it.type !is GenericTypeReference }
                .forEach { member ->
                    val memberParamType = (member.type?.asAstReference() ?: NamedTypeReference("Any")).intersect(refToTypeParameterForDecoratorMutability, generatedSourceLocation)
                    val boundTypeParam = TypeParameter(
                        TypeVariance.UNSPECIFIED,
                        IdentifierToken(contextCarry.findInternalTypeParameterName(member.name),  generatedSourceLocation),
                        memberParamType,
                    ).bindTo(contextCarry)
                    contextCarry = boundTypeParam.modifiedContext
                    additionalTypeParametersForDecoratedMembers[member] = boundTypeParam
                }
            fileContextWithAllTypeParameters = contextCarry
        } else {
            typeParameterForDecoratorMutability = null
            fileContextWithAllTypeParameters = fileContextWithTypeParametersDeclaredOnBaseType
        }
    }

    /*
    The contexts in a constructor:
    fileContext
      - constructorFunctionRootContext
        - contextWithSelfVar
            - contextWithParameters
     */
    override val functionRootContext: ExecutionScopedCTContext = ConstructorFunctionRootContext(fileContextWithAllTypeParameters)

    override val declaredAt get() = declaration.span
    override val receiverType = null
    override val declaresReceiver = false
    override val name get() = classDef.simpleName
    override val attributes = BoundFunctionAttributeList(fileContextWithAllTypeParameters, { this }, declaration.attributes)
    override val allTypeParameters: List<BoundTypeParameter> = declaredTypeParameters + listOfNotNull(typeParameterForDecoratorMutability) + additionalTypeParametersForDecoratedMembers.values

    /**
     * it is crucial that this collection sticks to the insertion order for the semantics of which mixin will implement
     * what supertypes. Kotlin 1.9 cannot deal with Java 21s SequencedSet, but maybe Kotlin 2 will
     */
    private val _mixins = mutableSetOf<BoundMixinStatement>()
    /** the mixins, in the order declared in the constructor */
    val mixins: Set<BoundMixinStatement> = _mixins

    private val exclusiveSelfBaseTypeRef by lazy {
        NamedTypeReference(
            classDef.simpleName,
            TypeReference.Nullability.NOT_NULLABLE,
            TypeMutability.EXCLUSIVE,
            classDef.declaration.name,
            classDef.typeParameters?.map {
                AstSpecificTypeArgument(
                    TypeVariance.UNSPECIFIED,
                    NamedTypeReference(it.astNode.name),
                )
            },
        )
    }
    override val returnType by lazy {
        functionRootContext.resolveType(if (typeParameterForDecoratorMutability != null) {
            AstIntersectionType(
                listOf(
                    exclusiveSelfBaseTypeRef.withMutability(TypeMutability.READONLY),
                    NamedTypeReference(IdentifierToken(typeParameterForDecoratorMutability.name, generatedSourceLocation)),
                ),
                generatedSourceLocation,
            )
        } else {
            exclusiveSelfBaseTypeRef
        })
    }

    /*
    The contexts in a constructor:
    classRootContext
      - constructorFunctionRootContext
        - contextWithSelfVar
            - contextWithParameters
        - contextAfterInitFromCtorParams
     */

    private val contextWithSelfVar = MutableExecutionScopedCTContext.deriveFrom(functionRootContext)
    private val selfVariableForInitCode: BoundVariable by lazy {
        val varAst = VariableDeclaration(
            generatedSourceLocation,
            null,
            null,
            null,
            IdentifierToken(BoundParameterList.RECEIVER_PARAMETER_NAME, generatedSourceLocation),
            exclusiveSelfBaseTypeRef,
            null,
        )
        val varInstance = varAst.bindToAsParameter(contextWithSelfVar)
        contextWithSelfVar.addVariable(varInstance)
        varInstance.defaultOwnership = VariableOwnership.BORROWED
        contextWithSelfVar.trackSideEffect(VariableInitialization.WriteToVariableEffect(varInstance))
        varInstance
    }

    override val parameters by lazy {
        val astParameters = classDef.memberVariables
            .filter { it.isConstructorParameterInitialized }
            .map { member ->
                val location = member.declaration.span.deriveGenerated()
                val type = additionalTypeParametersForDecoratedMembers[member]
                    ?.let { typeParam -> NamedTypeReference(IdentifierToken(typeParam.name, location)) }
                    ?: member.declaration.variableDeclaration.type?.withMutability(member.type?.mutability ?: TypeMutability.IMMUTABLE)
                    ?: NamedTypeReference("Any")
                VariableDeclaration(
                    location,
                    null,
                    null,
                    Pair(
                        VariableOwnership.CAPTURED,
                        KeywordToken(Keyword.CAPTURE, span = location),
                    ),
                    member.declaration.name,
                    type,
                    null,
                )
            }

        val astParameterList = ParameterList(astParameters)
        BoundParameterList(contextWithSelfVar, astParameterList, astParameterList.parameters.map { it.bindToAsConstructorParameter(contextWithSelfVar) })
    }

    private val boundMemberVariableInitCodeFromCtorParams: BoundCodeChunk by lazy {
        classDef.memberVariables
            .filter { it.isConstructorParameterInitialized }
            .map { memberVariable ->
                val generatedSourceLocation = memberVariable.initializer?.declaration?.span ?: memberVariable.declaredAt
                val parameter = parameters.parameters.single { it.name == memberVariable.name }
                AssignmentStatement(
                    KeywordToken(Keyword.SET, span = generatedSourceLocation),
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(selfVariableForInitCode.name, generatedSourceLocation)),
                        OperatorToken(Operator.DOT, generatedSourceLocation),
                        IdentifierToken(memberVariable.name, generatedSourceLocation),
                    ),
                    OperatorToken(Operator.EQUALS, generatedSourceLocation),
                    IdentifierExpression(IdentifierToken(parameter.name, generatedSourceLocation)),
                    considerSettersOnMemberVariableAssignment = false,
                )
            }
            .let(::AstCodeChunk)
            .bindTo(parameters.modifiedContext)
    }

    private val contextAfterInitFromCtorParams = MutableExecutionScopedCTContext.deriveFrom(contextWithSelfVar)
    private val boundMemberVariableInitCodeFromExpression: BoundCodeChunk by lazy {
        classDef.memberVariables
            .filterNot { it.isConstructorParameterInitialized }
            .filter { it.initializer != null  /* if null, there should be another error diagnosed for it */ }
            .map { memberVariable ->
                val generatedSourceLocation = memberVariable.initializer!!.declaration.span
                AssignmentStatement(
                    KeywordToken(Keyword.SET, span = generatedSourceLocation),
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(selfVariableForInitCode.name, generatedSourceLocation)),
                        OperatorToken(Operator.DOT, generatedSourceLocation),
                        IdentifierToken(memberVariable.name, generatedSourceLocation)
                    ),
                    OperatorToken(Operator.EQUALS, generatedSourceLocation),
                    memberVariable.initializer.declaration,
                    considerSettersOnMemberVariableAssignment = false,
                )
            }
            .let(::AstCodeChunk)
            .bindTo(contextAfterInitFromCtorParams)
    }

    private val additionalInitCode: BoundCodeChunk by lazy {
        declaration.code.bindTo(boundMemberVariableInitCodeFromExpression.modifiedContext)
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            // this has to be done first to make sure the type parameters are registered in the ctor function context
            allTypeParameters.forEach { it.semanticAnalysisPhase1(diagnosis) }

            attributes.semanticAnalysisPhase1(diagnosis)
            selfVariableForInitCode.semanticAnalysisPhase1(diagnosis)
            parameters.semanticAnalysisPhase1(diagnosis)
            boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase1(diagnosis)
            boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase1(diagnosis)
            additionalInitCode.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            allTypeParameters.forEach { it.semanticAnalysisPhase2(diagnosis) }

            selfVariableForInitCode.semanticAnalysisPhase2(diagnosis)
            contextWithSelfVar.trackSideEffect(PartialObjectInitialization.Effect.MarkObjectAsEntirelyUninitializedEffect(selfVariableForInitCode, classDef))

            /**
             * normally, we could rely on the assignments in boundMemberVariableInitCodeFromCtorParams to do their
             * part in tracking their initialization. However, the scope of the code that has access to the ctor params
             * is intentionally limited, so the information doesn't carry over. It has to be done again
             */
            classDef.memberVariables
                .asSequence()
                .filter { it.isConstructorParameterInitialized }
                .forEach {
                    contextAfterInitFromCtorParams.trackSideEffect(PartialObjectInitialization.Effect.WriteToMemberVariableEffect(selfVariableForInitCode, it))
                }

            attributes.semanticAnalysisPhase2(diagnosis)
            parameters.parameters.forEach { it.semanticAnalysisPhase2(diagnosis) }
            boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase2(diagnosis)
            boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase2(diagnosis)
            additionalInitCode.semanticAnalysisPhase2(diagnosis)

            if (attributes.isDeclaredNothrow) {
                diagnosis.constructorDeclaredNothrow(this)
            }
        }
    }

    override val purity = attributes.purity

    // this is for the memory allocation that can always throw OOM
    override val throwBehavior = SideEffectPrediction.POSSIBLY

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            allTypeParameters.forEach { it.semanticAnalysisPhase3(diagnosis) }

            attributes.semanticAnalysisPhase3(diagnosis)
            selfVariableForInitCode.semanticAnalysisPhase3(diagnosis)
            parameters.parameters.forEach { it.semanticAnalysisPhase3(diagnosis) }
            boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase3(diagnosis)
            boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase3(diagnosis)
            additionalInitCode.semanticAnalysisPhase3(diagnosis)

            if (BoundFunction.Purity.READONLY.contains(this.purity)) {
                val diagnosingVisitor = DiagnosingImpurityVisitor(diagnosis, PurityViolationDiagnostic.SideEffectBoundary.Function(this))
                handleCyclicInvocation(
                    context = this,
                    action = {
                        boundMemberVariableInitCodeFromExpression.visitWritesBeyond(
                            functionRootContext,
                            diagnosingVisitor
                        )
                        additionalInitCode.visitWritesBeyond(functionRootContext, diagnosingVisitor)
                    },
                    onCycle = {},
                )

                if (BoundFunction.Purity.PURE.contains(this.purity)) {
                    handleCyclicInvocation(
                        context = this,
                        action = {
                            boundMemberVariableInitCodeFromExpression.visitReadsBeyond(
                                functionRootContext,
                                diagnosingVisitor
                            )
                            additionalInitCode.visitReadsBeyond(functionRootContext, diagnosingVisitor)
                        },
                        onCycle = {},
                    )
                }
            }

            if (purity.contains(BoundFunction.Purity.MODIFYING)) {
                diagnosis.constructorDeclaredAsModifying(this)
            }

            val partialInitState = additionalInitCode.modifiedContext.getEphemeralState(PartialObjectInitialization, selfVariableForInitCode)
            classDef.memberVariables
                .filter { partialInitState.getMemberInitializationState(it) != VariableInitialization.State.INITIALIZED }
                .forEach {
                    diagnosis.add(ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic(it.declaration))
                }
        }
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        attributes.visibility.validateAccessFrom(location, this, diagnosis)
    }

    private val backendIr by lazy {
        val selfTemporary = IrCreateTemporaryValueImpl(IrAllocateObjectExpressionImpl(classDef))
        val initIr = ArrayList<IrExecutable>()
        initIr.add(IrUpdateSourceLocationStatementImpl(declaredAt))
        initIr.add(selfTemporary)
        if (classDef === functionRootContext.swCtx.weak) {
            check(additionalInitCode.statements.isEmpty()) {
                "Additional init code in ${classDef.canonicalName} is not supported"
            }
            val referencedObjTemporary = IrCreateTemporaryValueImpl(
                IrVariableAccessExpressionImpl(parameters.parameters.single().backendIrDeclaration)
            )
            initIr.add(referencedObjTemporary)
            initIr.add(IrAssignmentStatementImpl(
                IrAssignmentStatementTargetClassFieldImpl(
                    classDef.memberVariables.single().field.toBackendIr(),
                    IrTemporaryValueReferenceImpl(selfTemporary)
                ),
                IrTemporaryValueReferenceImpl(referencedObjTemporary),
            ))
            initIr.add(IrRegisterWeakReferenceStatementImpl(
                classDef.memberVariables.single(),
                IrTemporaryValueReferenceImpl(selfTemporary),
                IrTemporaryValueReferenceImpl(referencedObjTemporary),
            ))
        } else {
            initIr.add(selfVariableForInitCode.backendIrDeclaration)
            initIr.add(
                IrAssignmentStatementImpl(
                    IrAssignmentStatementTargetVariableImpl(selfVariableForInitCode.backendIrDeclaration),
                    IrTemporaryValueReferenceImpl(selfTemporary),
                )
            )
            initIr.add(boundMemberVariableInitCodeFromCtorParams.toBackendIrStatement())
            initIr.add(boundMemberVariableInitCodeFromExpression.toBackendIrStatement())
            initIr.add(additionalInitCode.toBackendIrStatement())
        }

        initIr.add(IrReturnStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)))

        IrDefaultConstructorImpl(
            this,
            IrCodeChunkImpl(initIr),
        )
    }

    override fun toBackendIr(): IrFunction = backendIr

    private inner class ConstructorFunctionRootContext(fileContextWithTypeParameters: CTContext) : MutableExecutionScopedCTContext(fileContextWithTypeParameters, true, true, ExecutionScopedCTContext.Repetition.EXACTLY_ONCE) {
        override fun registerMixin(mixinStatement: BoundMixinStatement, type: BoundTypeReference, diagnosis: Diagnosis): ExecutionScopedCTContext.MixinRegistration {
            _mixins.add(mixinStatement)

            when (val repetition = mixinStatement.context.getRepetitionBehaviorRelativeTo(this)) {
                ExecutionScopedCTContext.Repetition.EXACTLY_ONCE -> {
                    // all good
                }
                else -> diagnosis.illegalMixinRepetition(mixinStatement, repetition)
            }

            return object : ExecutionScopedCTContext.MixinRegistration {
                private lateinit var field: BaseTypeField
                override fun obtainField(): BaseTypeField {
                    if (!this::field.isInitialized) {
                        field = classDef.allocateField(type)
                    }

                    return field
                }

                override fun addDestructingAction(action: DestructorCodeGenerator) {
                    val dtor = classDef.destructor ?: throw InternalCompilerError("Destructor hasn't been initialized yet")
                    dtor.addDestructingAction(action)
                }
            }
        }
    }
}

private class IrClassSimpleType(
    val classDef: BoundBaseType,
    override val mutability: IrTypeMutability,
) : IrSimpleType {
    override val isNullable = false
    override val baseType get() = classDef.toBackendIr()
    override fun asNullable(): IrSimpleType = IrSimpleTypeImpl(baseType, mutability, true)
    override fun toString(): String = independentToString()
}

private class IrDefaultConstructorImpl(
    private val ctor: BoundClassConstructor,
    override val body: IrCodeChunk,
) : IrConstructor {
    override val canonicalName = ctor.canonicalName
    override val parameters = ctor.parameters.parameters.map { it.backendIrDeclaration }
    override val declaresReceiver = false
    override val returnType = IrClassSimpleType(ctor.classDef, IrTypeMutability.EXCLUSIVE)
    override val isExternalC = false
    override val isNothrow = ctor.attributes.isDeclaredNothrow
    override val ownerBaseType get() = ctor.classDef.toBackendIr()
    override val declaredAt = ctor.declaredAt
}

private class IrAllocateObjectExpressionImpl(val classDef: BoundBaseType) : IrAllocateObjectExpression {
    init {
        require(classDef.kind == BoundBaseType.Kind.CLASS)
    }
    override val clazz: IrClass by lazy { classDef.toBackendIr() as IrClass }
    override val evaluatesTo = IrClassSimpleType(classDef, IrTypeMutability.EXCLUSIVE)
}

private class IrRegisterWeakReferenceStatementImpl(
    holderMemberVariable: BoundBaseTypeMemberVariable,
    weakObjectTemporary: IrTemporaryValueReference,
    referredObjectTemporary: IrTemporaryValueReference,
) : IrRegisterWeakReferenceStatement {
    override val referenceStoredIn = object : IrAssignmentStatement.Target.ClassField {
        override val objectValue = weakObjectTemporary
        override val field = holderMemberVariable.field.toBackendIr()
    }

    override val referredObject = referredObjectTemporary
}