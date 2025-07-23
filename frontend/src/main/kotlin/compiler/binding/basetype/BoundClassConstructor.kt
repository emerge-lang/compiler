package compiler.binding.basetype

import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
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
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
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
import java.util.Collections

/**
 * The constructor of a class that, once compiled, does the basic bootstrapping:
 * 1. accept values for the constructor-initialized member variables
 * 2. allocate memory for the new object
 * 3. initialize all member variables as appropriate / as defined in their initializer expressions
 * 4. execute user-defined code additionally defined in a `constructor { ... }` block in the class definition
 */
class BoundClassConstructor(
    fileContextWithDeclaredTypeParameters: CTContext,
    private val constructorFunctionRootContext: ConstructorRootContext,
    override val declaredTypeParameters: List<BoundTypeParameter>,
    private val typeParameterForDecoratorMutability: BoundTypeParameter?,
    private val additionalTypeParameters: List<BoundTypeParameter>,
    override val parameters: BoundParameterList,
    private val selfVariableForInitCode: BoundVariable,
    private val mutableContextBeforeInitCode: MutableExecutionScopedCTContext,
    val boundInitCode: BoundCodeChunk,
    private val mutableContextBeforeBody: MutableExecutionScopedCTContext,
    val boundBody: BoundCodeChunk,
    override val entryDeclaration: BaseTypeConstructorDeclaration,
    val buildReceiverType: (Span) -> AstAbsoluteTypeReference,
    getClassDef: () -> BoundBaseType,
) : BoundFunction, BoundBaseTypeEntry<BaseTypeConstructorDeclaration> {
    override val parentContext = fileContextWithDeclaredTypeParameters

    val classDef: BoundBaseType by lazy(getClassDef)
    private val generatedSourceLocation = entryDeclaration.span.deriveGenerated()
    override val canonicalName: CanonicalElementName.Function by lazy {
        CanonicalElementName.Function(classDef.canonicalName, "\$constructor")
    }
    override val functionRootContext = constructorFunctionRootContext

    override val declaredAt get() = entryDeclaration.span
    override val receiverType = null
    override val declaresReceiver = false
    override val name get() = classDef.simpleName
    override val attributes = BoundFunctionAttributeList(constructorFunctionRootContext, { this }, entryDeclaration.attributes)
    override val allTypeParameters: List<BoundTypeParameter> = declaredTypeParameters + listOfNotNull(typeParameterForDecoratorMutability) + additionalTypeParameters

    val mixins: Set<BoundMixinStatement> = constructorFunctionRootContext.mixins

    private val exclusiveSelfBaseTypeRef by lazy {
        parentContext.resolveType(
            buildReceiverType(declaredAt)
                .withMutability(TypeMutability.EXCLUSIVE)
        )
    }
    override val returnType by lazy {
        if (typeParameterForDecoratorMutability == null) {
            return@lazy exclusiveSelfBaseTypeRef
        }

        exclusiveSelfBaseTypeRef.intersect(GenericTypeReference(
            NamedTypeReference(IdentifierToken(typeParameterForDecoratorMutability.name, generatedSourceLocation)),
            typeParameterForDecoratorMutability,
        ))
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            // this has to be done first to make sure the type parameters are registered in the ctor function context
            allTypeParameters.forEach { it.semanticAnalysisPhase1(diagnosis) }

            attributes.semanticAnalysisPhase1(diagnosis)
            selfVariableForInitCode.semanticAnalysisPhase1(diagnosis)
            parameters.semanticAnalysisPhase1(diagnosis)
            boundInitCode.semanticAnalysisPhase1(diagnosis)
            boundBody.semanticAnalysisPhase1(diagnosis)

            // this is necessary because the context structure hides the member variable initializations from
            // ctor parameters. This hiding is also necessary.
            mutableContextBeforeInitCode.trackSideEffect(VariableInitialization.WriteToVariableEffect(selfVariableForInitCode))
            mutableContextBeforeInitCode.trackSideEffect(PartialObjectInitialization.Effect.MarkObjectAsEntirelyUninitializedEffect(selfVariableForInitCode, classDef))

            /**
             * normally, we could rely on the assignments in boundInitCode to do their part in tracking their
             * initialization. However, the scope of the code that has access to the ctor params is intentionally limited,
             * so the information doesn't carry over. It has to be done again.
             */
            mutableContextBeforeBody.trackSideEffect(VariableInitialization.WriteToVariableEffect(selfVariableForInitCode))
            mutableContextBeforeBody.trackSideEffect(PartialObjectInitialization.Effect.MarkObjectAsEntirelyUninitializedEffect(selfVariableForInitCode, classDef))
            classDef.memberVariables
                .asSequence()
                .filter { it.isConstructorParameterInitialized }
                .forEach {
                    mutableContextBeforeBody.trackSideEffect(PartialObjectInitialization.Effect.WriteToMemberVariableEffect(selfVariableForInitCode, it))
                }
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            allTypeParameters.forEach { it.semanticAnalysisPhase2(diagnosis) }

            attributes.semanticAnalysisPhase2(diagnosis)
            selfVariableForInitCode.semanticAnalysisPhase2(diagnosis)
            parameters.parameters.forEach { it.semanticAnalysisPhase2(diagnosis) }
            boundInitCode.semanticAnalysisPhase2(diagnosis)
            boundBody.semanticAnalysisPhase2(diagnosis)

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
            boundInitCode.semanticAnalysisPhase3(diagnosis)
            boundBody.semanticAnalysisPhase3(diagnosis)

            if (BoundFunction.Purity.READONLY.contains(this.purity)) {
                val diagnosingVisitor = DiagnosingImpurityVisitor(diagnosis, PurityViolationDiagnostic.SideEffectBoundary.Function(this))
                handleCyclicInvocation(
                    context = this,
                    action = {
                        boundInitCode.visitWritesBeyond(
                            functionRootContext,
                            diagnosingVisitor
                        )
                        boundBody.visitWritesBeyond(functionRootContext, diagnosingVisitor)
                    },
                    onCycle = {},
                )

                if (BoundFunction.Purity.PURE.contains(this.purity)) {
                    handleCyclicInvocation(
                        context = this,
                        action = {
                            boundInitCode.visitReadsBeyond(
                                functionRootContext,
                                diagnosingVisitor
                            )
                            boundBody.visitReadsBeyond(functionRootContext, diagnosingVisitor)
                        },
                        onCycle = {},
                    )
                }
            }

            if (purity.contains(BoundFunction.Purity.MODIFYING)) {
                diagnosis.constructorDeclaredAsModifying(this)
            }

            val partialInitState = boundBody.modifiedContext.getEphemeralState(PartialObjectInitialization, selfVariableForInitCode)
            partialInitState.getUninitializedMembers(classDef).forEach {
                diagnosis.add(ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic(it.entryDeclaration))
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
            check(boundBody.statements.isEmpty()) {
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
            initIr.add(boundInitCode.toBackendIrStatement())
            initIr.add(boundBody.toBackendIrStatement())
        }

        initIr.add(IrReturnStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)))

        IrDefaultConstructorImpl(
            this,
            IrCodeChunkImpl(initIr),
        )
    }

    override fun toBackendIr(): IrFunction = backendIr

    override fun toString() = canonicalName.toString()

    class ConstructorRootContext(
        typeRootContextWithAllCtorTypeParameters: CTContext,
        private val getClassDef: () -> BoundBaseType,
    ) : MutableExecutionScopedCTContext(typeRootContextWithAllCtorTypeParameters, true, true, ExecutionScopedCTContext.Repetition.EXACTLY_ONCE) {
        private val _mixins = mutableSetOf<BoundMixinStatement>()
        val mixins: Set<BoundMixinStatement> = Collections.unmodifiableSet(_mixins)

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
                        field = getClassDef().allocateField(type)
                    }

                    return field
                }

                override fun addDestructingAction(action: DestructorCodeGenerator) {
                    getClassDef().destructor?.addDestructingAction(action)
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