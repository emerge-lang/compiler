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
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.IrClassMemberVariableAccessExpressionImpl
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Span
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDeallocateObjectStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrUnregisterWeakReferenceStatement

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
                    IdentifierToken("borrow", generatedSourceLocation),
                ),
                IdentifierToken("self", generatedSourceLocation),
                (receiverType as RootResolvedTypeReference).original!!.withMutability(TypeMutability.EXCLUSIVE),
                null,
            )
        ))
        astParameterList.bindTo(destructorFunctionRootContext).also {
            check(it.semanticAnalysisPhase1().isEmpty())
        }
    }

    val userDefinedCode: BoundCodeChunk by lazy {
        declaration.code.bindTo(parameters.modifiedContext)
    }

    override val purity = BoundFunction.Purity.MODIFYING
    override val throwBehavior: SideEffectPrediction? get() {
        if (attributes.isDeclaredNothrow) {
            return SideEffectPrediction.NEVER
        }
        return userDefinedCode.throwBehavior
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            userDefinedCode.semanticAnalysisPhase1()
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = userDefinedCode.semanticAnalysisPhase2()
            if (attributes.isDeclaredNothrow) {
                userDefinedCode.setNothrow(NothrowViolationReporting.SideEffectBoundary.Function(this))
            }
            return@phase2 reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableListOf<Reporting>()
            reportings.addAll(userDefinedCode.semanticAnalysisPhase3())
            if (attributes.isDeclaredNothrow) {
                val boundary = NothrowViolationReporting.SideEffectBoundary.Function(this)
                classDef.memberVariables
                    .filter { it.type?.destructorThrowBehavior != SideEffectPrediction.NEVER }
                    .forEach { reportings.add(Reporting.droppingReferenceToObjectWithThrowingConstructor(it, classDef, boundary))}
            }

            return@phase3 reportings
        }
    }

    override fun validateAccessFrom(location: Span): Collection<Reporting> {
        throw InternalCompilerError("Access checks on destructors are not supposed to happen")
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
                        IrClassMemberVariableAccessExpressionImpl(
                            IrTemporaryValueReferenceImpl(selfTemporary),
                            holderMemberVar.toBackendIr(),
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

        val destructorCode = IrCodeChunkImpl(listOfNotNull(
            userDefinedCode.toBackendIrStatement(),
            selfTemporary,
            IrCodeChunkImpl(classDef.memberVariables.flatMap { memberVar ->
                val memberTemporary = IrCreateTemporaryValueImpl(
                    IrClassMemberVariableAccessExpressionImpl(
                        IrTemporaryValueReferenceImpl(selfTemporary),
                        memberVar.toBackendIr(),
                        memberVar.type!!.toBackendIr(),
                    )
                )
                listOf(
                    memberTemporary,
                    IrDropStrongReferenceStatementImpl(memberTemporary),
                )
            }),
            IrDeallocateObjectStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)),
        ))

        IrDestructorImpl(this, destructorCode)
    }
    override fun toBackendIr(): IrFunction {
        return backendIr
    }
}

private class IrDestructorImpl(
    val dtor: BoundClassDestructor,
    override val body: IrCodeChunk,
) : IrMemberFunction {
    override val canonicalName = dtor.canonicalName
    override val parameters = dtor.parameters.parameters.map { it.backendIrDeclaration }
    override val returnType = dtor.returnType.toBackendIr()
    override val isExternalC = false
    override val declaredOn get() = dtor.classDef.toBackendIr()
    override val overrides = emptySet<IrMemberFunction>()
    override val supportsDynamicDispatch = true
}

private class IrDeallocateObjectStatementImpl(
    override val value: IrTemporaryValueReference
) : IrDeallocateObjectStatement

private class IrUnregisterWeakReferenceStatementImpl(
    holderMemberVariable: BoundBaseTypeMemberVariable,
    weakObjectTemporary: IrTemporaryValueReference,
    referredObjectTemporary: IrTemporaryValueReference,
) : IrUnregisterWeakReferenceStatement {
    override val referenceStoredIn = object : IrAssignmentStatement.Target.ClassMemberVariable {
        override val objectValue = weakObjectTemporary
        override val memberVariable = holderMemberVariable.toBackendIr()
    }

    override val referredObject = referredObjectTemporary
}