package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.BaseTypeDestructorDeclaration
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.VariableOwnership
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundParameterList
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.IrClassFieldAccessExpressionImpl
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDeallocateObjectStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrUnregisterWeakReferenceStatement
import io.github.tmarsteel.emerge.common.CanonicalElementName

class BoundClassDestructor(
    private val fileContextWithTypeParameters: CTContext,
    override val declaredTypeParameters: List<BoundTypeParameter>,
    getClassDef: () -> BoundBaseType,
    override val attributes: BoundFunctionAttributeList,
    val declaration: BaseTypeDestructorDeclaration,
) : BoundFunction, BoundBaseTypeEntry<BaseTypeDestructorDeclaration> {
    val classDef: BoundBaseType by lazy(getClassDef)
    override val declaredAt = declaration.span
    private val generatedSourceLocation = declaredAt.deriveGenerated()
    override val canonicalName: CanonicalElementName.Function by lazy {
        CanonicalElementName.Function(classDef.canonicalName, "\$destructor")
    }

    override val context = fileContextWithTypeParameters
    private val destructorFunctionRootContext = MutableExecutionScopedCTContext.functionRootIn(fileContextWithTypeParameters)

    override val declaresReceiver = true
    override val receiverType by lazy {
        destructorFunctionRootContext.resolveType(
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
    override val name by lazy { "__${classDef.simpleName}__finalize" }
    override val allTypeParameters = declaredTypeParameters
    override val returnType get() = fileContextWithTypeParameters.swCtx.unit.baseReference

    override val parameters by lazy {
        val astParameterList = ParameterList(listOf(
            VariableDeclaration(
                generatedSourceLocation,
                null,
                null,
                Pair(
                    VariableOwnership.BORROWED,
                    KeywordToken(Keyword.BORROW, span = generatedSourceLocation),
                ),
                IdentifierToken(BoundParameterList.RECEIVER_PARAMETER_NAME, generatedSourceLocation),
                (receiverType as RootResolvedTypeReference).original!!.withMutability(TypeMutability.EXCLUSIVE),
                null,
            )
        ))
        astParameterList.bindTo(destructorFunctionRootContext)
    }

    val userDefinedCode: BoundCodeChunk by lazy {
        declaration.code.bindTo(parameters.modifiedContext)
    }

    override val purity = BoundFunction.Purity.MODIFYING
    override val throwBehavior: SideEffectPrediction = SideEffectPrediction.NEVER

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            userDefinedCode.semanticAnalysisPhase1(diagnosis)
            parameters.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            userDefinedCode.semanticAnalysisPhase2(diagnosis)

            userDefinedCode.setNothrow(NothrowViolationDiagnostic.SideEffectBoundary.Function(this))
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            userDefinedCode.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        throw InternalCompilerError("Access checks on destructors are not supposed to happen")
    }

    private val additionalCode = mutableListOf<DestructorCodeGenerator>()

    /**
     * The given action will be executed after the regular destruction process of the class.
     * @param generateAction first parameter: a temporary holding a reference to the object being destructured (self)
     */
    fun addDestructingAction(action: DestructorCodeGenerator) {
        additionalCode.add(action)
    }

    private val backendIr by lazy {
        val selfTemporary = IrCreateTemporaryValueImpl(
            IrVariableAccessExpressionImpl(parameters.parameters.single().backendIrDeclaration)
        )
        if (classDef === context.swCtx.weak) {
            return@lazy IrDestructorImpl(this, IrCodeChunkImpl(listOf(
                userDefinedCode.toBackendIrStatement(),
                selfTemporary,
                classDef.memberVariables.single().let { holderMemberVar ->
                    val referredObjectTemporary = IrCreateTemporaryValueImpl(
                        IrClassFieldAccessExpressionImpl(
                            IrTemporaryValueReferenceImpl(selfTemporary),
                            holderMemberVar.field.toBackendIr(),
                            holderMemberVar.type!!.toBackendIr(),
                        )
                    )
                    IrCodeChunkImpl(listOf(
                        referredObjectTemporary,
                        IrUnregisterWeakReferenceStatementImpl(
                            classDef.memberVariables.single(),
                            IrTemporaryValueReferenceImpl(selfTemporary),
                            IrTemporaryValueReferenceImpl(referredObjectTemporary),
                        )
                    ))
                },
                IrDeallocateObjectStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary))
            )))
        }

        val additionalCode = additionalCode.map { gen -> gen(selfTemporary) }
        val destructorCode = IrCodeChunkImpl(listOfNotNull(
            userDefinedCode.toBackendIrStatement(),
            selfTemporary,
            IrCodeChunkImpl(classDef.memberVariables.flatMap { memberVar ->
                val memberTemporary = IrCreateTemporaryValueImpl(
                    IrClassFieldAccessExpressionImpl(
                        IrTemporaryValueReferenceImpl(selfTemporary),
                        memberVar.field.toBackendIr(),
                        memberVar.type!!.toBackendIr(),
                    )
                )
                listOf(
                    memberTemporary,
                    IrDropStrongReferenceStatementImpl(memberTemporary),
                )
            }),
        ) + additionalCode + listOf(
            IrDeallocateObjectStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)),
        ))

        IrDestructorImpl(this, destructorCode)
    }
    override fun toBackendIr(): IrFunction {
        return backendIr
    }
}

typealias DestructorCodeGenerator = (self: IrCreateTemporaryValue) -> IrExecutable

private class IrDestructorImpl(
    val dtor: BoundClassDestructor,
    override val body: IrCodeChunk,
) : IrMemberFunction {
    override val canonicalName = dtor.canonicalName
    override val parameters = dtor.parameters.parameters.map { it.backendIrDeclaration }
    override val declaresReceiver = true
    override val returnType = dtor.returnType.toBackendIr()
    override val isExternalC = false
    override val isNothrow = dtor.attributes.isDeclaredNothrow
    override val ownerBaseType get() = dtor.classDef.toBackendIr()
    override val overrides = emptySet<IrMemberFunction>()
    override val supportsDynamicDispatch = true
    override val declaredAt = dtor.declaredAt
}

private class IrDeallocateObjectStatementImpl(
    override val value: IrTemporaryValueReference
) : IrDeallocateObjectStatement

private class IrUnregisterWeakReferenceStatementImpl(
    holderMemberVariable: BoundBaseTypeMemberVariable,
    weakObjectTemporary: IrTemporaryValueReference,
    referredObjectTemporary: IrTemporaryValueReference,
) : IrUnregisterWeakReferenceStatement {
    override val referenceStoredIn = object : IrAssignmentStatement.Target.ClassField {
        override val objectValue = weakObjectTemporary
        override val field = holderMemberVariable.field.toBackendIr()
    }

    override val referredObject = referredObjectTemporary
}