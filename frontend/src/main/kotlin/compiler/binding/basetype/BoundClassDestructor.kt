package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.AstFunctionAttribute
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
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.IrClassMemberVariableAccessExpressionImpl
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDeallocateObjectStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class BoundClassDestructor(
    private val fileContextWithTypeParameters: CTContext,
    override val declaredTypeParameters: List<BoundTypeParameter>,
    getClassDef: () -> BoundBaseTypeDefinition,
    val declaration: BaseTypeDestructorDeclaration,
) : BoundFunction, BoundBaseTypeEntry<BaseTypeDestructorDeclaration> {
    val classDef: BoundBaseTypeDefinition by lazy(getClassDef)
    override val declaredAt = declaration.sourceLocation
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
                classDef.typeParameters.map {
                    TypeArgument(
                        TypeVariance.UNSPECIFIED,
                        TypeReference(it.astNode.name),
                    )
                },
            ),
        )
    }
    override val name by lazy { "__${classDef.simpleName}__finalize" }
    override val attributes = BoundFunctionAttributeList(
        fileContextWithTypeParameters,
        listOf(
            AstFunctionAttribute.EffectCategory(
                AstFunctionAttribute.EffectCategory.Category.MODIFYING,
                KeywordToken(Keyword.MUTABLE),
            ),
        ),
    )
    override val allTypeParameters = declaredTypeParameters
    override val returnType get() = fileContextWithTypeParameters.swCtx.unitBaseType.baseReference

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

    override val isPure = false
    override val isReadonly = false
    override val isGuaranteedToThrow get() = userDefinedCode.isGuaranteedToThrow ?: false

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return userDefinedCode.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return userDefinedCode.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return userDefinedCode.semanticAnalysisPhase3()
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        throw InternalCompilerError("Access checks on destructors are not supposed to happen")
    }

    private val backendIr by lazy {
        val selfTemporary = IrCreateTemporaryValueImpl(
            IrVariableAccessExpressionImpl(parameters.parameters.single().backendIrDeclaration)
        )
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
                    IrDropReferenceStatementImpl(memberTemporary),
                )
            }),
            IrDeallocateObjectStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary))
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
) : IrFunction {
    override val canonicalName = dtor.canonicalName
    override val parameters = dtor.parameters.parameters.map { it.backendIrDeclaration }
    override val returnType = dtor.returnType.toBackendIr()
    override val isExternalC = false
}

private class IrDeallocateObjectStatementImpl(
    override val value: IrTemporaryValueReference
) : IrDeallocateObjectStatement