package compiler.binding.basetype

import compiler.ast.AssignmentStatement
import compiler.ast.BaseTypeConstructorDeclaration
import compiler.ast.CodeChunk
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.VariableOwnership
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundStatement
import compiler.binding.BoundVariable
import compiler.binding.IrAssignmentStatementImpl
import compiler.binding.IrAssignmentStatementTargetVariableImpl
import compiler.binding.IrCodeChunkImpl
import compiler.binding.IrReturnStatementImpl
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.handleCyclicInvocation
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.SourceLocation
import compiler.reportings.ClassMemberVariableNotInitializedDuringObjectConstructionReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType

/**
 * The constructor of a class that, once compiled, does the basic bootstrapping:
 * 1. accept values for the constructor-initialized member variables
 * 2. allocate the appropriate amount of memory
 * 3. initialize all member variables as appropriate / as defined in their initializer expressions
 * 4. execute user-defined code additionally defined in a `constructor { ... }` block in the class definition
 */
class BoundClassConstructor(
    private val fileContextWithTypeParameters: CTContext,
    override val declaredTypeParameters: List<BoundTypeParameter>,
    getClassDef: () -> BoundBaseType,
    val declaration: BaseTypeConstructorDeclaration,
) : BoundFunction, BoundBaseTypeEntry<BaseTypeConstructorDeclaration> {
    val classDef: BoundBaseType by lazy(getClassDef)
    private val generatedSourceLocation = declaration.sourceLocation.deriveGenerated()
    override val canonicalName: CanonicalElementName.Function by lazy {
        CanonicalElementName.Function(classDef.canonicalName, "\$constructor")
    }

    /*
    The contexts in a constructor:
    fileContext
      - constructorFunctionRootContext
        - contextWithSelfVar
            - contextWithParameters
     */
    private val constructorFunctionRootContext = MutableExecutionScopedCTContext.functionRootIn(fileContextWithTypeParameters)
    override val context = fileContextWithTypeParameters

    override val declaredAt get() = declaration.sourceLocation
    override val receiverType = null
    override val declaresReceiver = false
    override val name get() = classDef.simpleName
    override val attributes = BoundFunctionAttributeList(fileContextWithTypeParameters, declaration.attributes)
    override val allTypeParameters = declaredTypeParameters

    override val returnType by lazy {
        constructorFunctionRootContext.resolveType(
            TypeReference(
                classDef.simpleName,
                TypeReference.Nullability.NOT_NULLABLE,
                TypeMutability.EXCLUSIVE,
                classDef.declaration.name,
                classDef.typeParameters?.map {
                    TypeArgument(
                        TypeVariance.UNSPECIFIED,
                        TypeReference(it.astNode.name),
                    )
                },
            ),
        )
    }

    /*
    The contexts in a constructor:
    classRootContext
      - constructorFunctionRootContext
        - contextWithSelfVar
            - contextWithParameters
        - contextAfterInitFromCtorParams
     */

    private val contextWithSelfVar = MutableExecutionScopedCTContext.deriveFrom(constructorFunctionRootContext)
    private val selfVariableForInitCode: BoundVariable by lazy {
        val varAst = VariableDeclaration(
            generatedSourceLocation,
            null,
            null,
            null,
            IdentifierToken("self", generatedSourceLocation),
            (returnType as RootResolvedTypeReference).original!!.withMutability(TypeMutability.EXCLUSIVE),
            null,
        )
        val varInstance = varAst.bindTo(contextWithSelfVar, BoundVariable.Kind.PARAMETER)
        contextWithSelfVar.addVariable(varInstance)
        varInstance.defaultOwnership = VariableOwnership.BORROWED
        contextWithSelfVar.trackSideEffect(VariableInitialization.WriteToVariableEffect(varInstance))
        varInstance
    }

    override val parameters by lazy {
        val astParameterList = ParameterList(classDef.memberVariables
            .filter { it.isConstructorParameterInitialized }
            .map { member ->
                val location = member.declaration.sourceLocation.deriveGenerated()
                VariableDeclaration(
                    location,
                    null,
                    null,
                    Pair(
                        VariableOwnership.CAPTURED,
                        IdentifierToken("capture", location),
                    ),
                    member.declaration.name,
                    member.declaration.variableDeclaration.type?.withMutability(member.type?.mutability ?: TypeMutability.IMMUTABLE)
                        ?: TypeReference("Any"),
                    null,
                )
            })
        astParameterList.bindTo(contextWithSelfVar).also {
            check(it.semanticAnalysisPhase1().isEmpty())
        }
    }

    private val boundMemberVariableInitCodeFromCtorParams: BoundCodeChunk by lazy {
        classDef.memberVariables
            .filter { it.isConstructorParameterInitialized }
            .map { memberVariable ->
                val parameter = parameters.parameters.single { it.name == memberVariable.name }
                AssignmentStatement(
                    KeywordToken(Keyword.SET, sourceLocation = generatedSourceLocation),
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(selfVariableForInitCode.name, generatedSourceLocation)),
                        OperatorToken(Operator.DOT, generatedSourceLocation),
                        IdentifierToken(memberVariable.name, generatedSourceLocation),
                    ),
                    OperatorToken(Operator.EQUALS, generatedSourceLocation),
                    IdentifierExpression(IdentifierToken(parameter.name, generatedSourceLocation)),
                )
            }
            .let(::CodeChunk)
            .bindTo(parameters.modifiedContext)
    }

    private val contextAfterInitFromCtorParams = MutableExecutionScopedCTContext.deriveFrom(contextWithSelfVar)
    private val boundMemberVariableInitCodeFromExpression: BoundCodeChunk by lazy {
        classDef.memberVariables
            .filterNot { it.isConstructorParameterInitialized }
            .filter { it.initializer != null  /* if null, there should be another error diagnosed for it */ }
            .map { memberVariable ->
                AssignmentStatement(
                    KeywordToken(Keyword.SET, sourceLocation = generatedSourceLocation),
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(selfVariableForInitCode.name, generatedSourceLocation)),
                        OperatorToken(Operator.DOT, generatedSourceLocation),
                        IdentifierToken(memberVariable.name, generatedSourceLocation)
                    ),
                    OperatorToken(Operator.EQUALS, generatedSourceLocation),
                    memberVariable.initializer!!.declaration,
                )
            }
            .let(::CodeChunk)
            .bindTo(contextAfterInitFromCtorParams)
    }

    private val additionalInitCode: BoundCodeChunk by lazy {
        declaration.code.bindTo(boundMemberVariableInitCodeFromExpression.modifiedContext)
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableListOf<Reporting>()
            // this has to be done first to make sure the type parameters are registered in the ctor function context
            declaredTypeParameters.map { it.semanticAnalysisPhase1() }.forEach(reportings::addAll)

            reportings.addAll(attributes.semanticAnalysisPhase1())
            reportings.addAll(selfVariableForInitCode.semanticAnalysisPhase1())
            reportings.addAll(boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase1())
            reportings.addAll(boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase1())
            additionalInitCode.semanticAnalysisPhase1().let(reportings::addAll)

            reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = mutableListOf<Reporting>()
            declaredTypeParameters.map { it.semanticAnalysisPhase2() }.forEach(reportings::addAll)

            reportings.addAll(selfVariableForInitCode.semanticAnalysisPhase2())
            contextWithSelfVar.trackSideEffect(PartialObjectInitialization.Effect.MarkObjectAsEntireUninitializedEffect(selfVariableForInitCode, classDef))

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

            reportings.addAll(attributes.semanticAnalysisPhase2())
            reportings.addAll(boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase2())
            reportings.addAll(boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase2())
            reportings.addAll(additionalInitCode.semanticAnalysisPhase2())

            reportings
        }
    }

    private var isEffectivelyPure: Boolean? = null
        private set

    private var isEffectivelyReadonly: Boolean? = null
        private set

    override val purity = attributes.purity

    override val isGuaranteedToThrow get() = boundMemberVariableInitCodeFromExpression.isGuaranteedToThrow || additionalInitCode.isGuaranteedToThrow

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableListOf<Reporting>()
            declaredTypeParameters.map { it.semanticAnalysisPhase2() }.forEach(reportings::addAll)

            reportings.addAll(attributes.semanticAnalysisPhase3())
            reportings.addAll(selfVariableForInitCode.semanticAnalysisPhase3())
            reportings.addAll(boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase3())
            reportings.addAll(boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase3())
            reportings.addAll(additionalInitCode.semanticAnalysisPhase3())

            if (BoundFunction.Purity.READONLY.contains(this.purity)) {
                val statementsWritingBeyondConstructorContext: Collection<BoundStatement<*>> = handleCyclicInvocation(
                    this,
                    action = {
                        boundMemberVariableInitCodeFromExpression.findWritesBeyond(constructorFunctionRootContext) +
                                additionalInitCode.findWritesBeyond(constructorFunctionRootContext)
                    },
                    onCycle = ::emptySet,
                )

                if (BoundFunction.Purity.PURE.contains(this.purity)) {
                    val statementsReadingBeyondConstructorContext: Collection<BoundExpression<*>> = handleCyclicInvocation(
                        this,
                        action = {
                            boundMemberVariableInitCodeFromExpression.findReadsBeyond(constructorFunctionRootContext) +
                                    additionalInitCode.findReadsBeyond(constructorFunctionRootContext)
                        },
                        onCycle = ::emptySet,
                    )

                    reportings.addAll(Reporting.purityViolations(statementsReadingBeyondConstructorContext, statementsWritingBeyondConstructorContext, this))
                } else {
                    reportings.addAll(Reporting.readonlyViolations(statementsWritingBeyondConstructorContext, this))
                }
            }

            if (purity.contains(BoundFunction.Purity.MODIFYING)) {
                reportings.add(Reporting.constructorDeclaredAsModifying(this))
            }

            val partialInitState = additionalInitCode.modifiedContext.getEphemeralState(PartialObjectInitialization, selfVariableForInitCode)
            classDef.memberVariables
                .filter { partialInitState.getMemberInitializationState(it) != VariableInitialization.State.INITIALIZED }
                .forEach {
                    reportings.add(ClassMemberVariableNotInitializedDuringObjectConstructionReporting(it.declaration))
                }

            reportings
        }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return attributes.visibility.validateAccessFrom(location, this)
    }

    private val backendIr by lazy {
        val selfTemporary = IrCreateTemporaryValueImpl(IrAllocateObjectExpressionImpl(classDef))
        val initIr = ArrayList<IrExecutable>()
        initIr.add(selfTemporary)
        initIr.add(selfVariableForInitCode.backendIrDeclaration)
        initIr.add(IrAssignmentStatementImpl(
            IrAssignmentStatementTargetVariableImpl(selfVariableForInitCode.backendIrDeclaration),
            IrTemporaryValueReferenceImpl(selfTemporary),
        ))
        initIr.add(boundMemberVariableInitCodeFromCtorParams.toBackendIrStatement())
        initIr.add(boundMemberVariableInitCodeFromExpression.toBackendIrStatement())
        initIr.add(additionalInitCode.toBackendIrStatement())

        IrDefaultConstructorImpl(
            this,
            IrCodeChunkImpl(listOfNotNull(
                IrCodeChunkImpl(initIr),
                IrReturnStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)),
            ))
        )
    }
    override fun toBackendIr(): IrFunction = backendIr
}

private class IrClassSimpleType(val classDef: BoundBaseType) : IrSimpleType {
    override val isNullable = false
    override val baseType get() = classDef.toBackendIr()
}

private class IrDefaultConstructorImpl(
    ctor: BoundClassConstructor,
    override val body: IrCodeChunk,
) : IrFunction {
    override val canonicalName = ctor.canonicalName
    override val parameters = ctor.parameters.parameters.map { it.backendIrDeclaration }
    override val returnType = IrClassSimpleType(ctor.classDef)
    override val isExternalC = false
}

private class IrAllocateObjectExpressionImpl(val classDef: BoundBaseType) : IrAllocateObjectExpression {
    init {
        require(classDef.kind == BoundBaseType.Kind.CLASS)
    }
    override val clazz: IrClass by lazy { classDef.toBackendIr() as IrClass }
    override val evaluatesTo = object : IrSimpleType {
        override val isNullable = false
        override val baseType get() = this@IrAllocateObjectExpressionImpl.clazz
    }
}