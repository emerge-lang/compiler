package compiler.binding.classdef

import compiler.ast.CodeChunk
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundVariable
import compiler.binding.IrAssignmentStatementImpl
import compiler.binding.IrAssignmentStatementTargetClassMemberVariableImpl
import compiler.binding.IrAssignmentStatementTargetVariableImpl
import compiler.binding.IrCodeChunkImpl
import compiler.binding.IrReturnStatementImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType

/**
 * The constructor of a class that, once compiled, does the basic bootstrapping:
 * 1. accept values for the constructor-initialized member variables
 * 2. allocate the appropriate amount of memory
 * 3. initialize all member variables as appropriate / as defined in their initializer expressions
 * 4. execute user-defined code additionally defined in a `constructor { ... }` block in the class definition
 */
class BoundClassDefaultConstructor(
    val classDef: BoundClassDefinition,
    val additionalInitCodeAst: CodeChunk?,
) : BoundFunction() {
    override val context: CTContext = MutableCTContext(classDef.classRootContext)
    val constructorFunctionRootContext: ExecutionScopedCTContext = MutableExecutionScopedCTContext.functionRootIn(context)
    override val declaredAt = classDef.declaration.declaredAt
    override val receiverType = null
    override val declaresReceiver = false
    override val name = classDef.simpleName
    override val attributes = BoundFunctionAttributeList(emptyList())
    override val isPure = true
    override val isReadonly = true
    override val returnsExclusiveValue = true
    override val isGuaranteedToThrow = false
    override val typeParameters: List<BoundTypeParameter>
        get() = classDef.typeParameters
    override val parameters = run {
        val astParameterList = ParameterList(classDef.memberVariables
            .filter { it.isDefaultConstructorInitialized }
            .map { member ->
                VariableDeclaration(
                    member.declaration.declaredAt,
                    null,
                    member.declaration.name,
                    member.declaration.variableDeclaration.type!!,
                    null,
                )
            })
        astParameterList.bindTo(constructorFunctionRootContext).also {
            it.semanticAnalysisPhase1()
        }
    }

    override val returnType = context.resolveType(
        TypeReference(
            classDef.simpleName,
            TypeReference.Nullability.NOT_NULLABLE,
            TypeMutability.IMMUTABLE,
            classDef.declaration.name,
            classDef.typeParameters.map {
                TypeArgument(
                    TypeVariance.UNSPECIFIED,
                    TypeReference(it.astNode.name),
                )
            },
        ),
    )

    private val contextForAdditionalInitCode: ExecutionScopedCTContext
    private val selfVariableForAdditionalInitCode: BoundVariable
    init {
        val contextWithSelfVar = MutableExecutionScopedCTContext.deriveFrom(constructorFunctionRootContext)
        contextForAdditionalInitCode = contextWithSelfVar
        selfVariableForAdditionalInitCode = contextWithSelfVar.addVariable(VariableDeclaration(
            classDef.declaration.declaredAt,
            null,
            IdentifierToken("self"),
            (returnType as RootResolvedTypeReference).original!!.withMutability(TypeMutability.MUTABLE),
            null,
        ))
    }
    private val additionalInitCode = additionalInitCodeAst?.bindTo(contextForAdditionalInitCode)

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        check(selfVariableForAdditionalInitCode.semanticAnalysisPhase1().isEmpty())
        val reportings = mutableListOf<Reporting>()
        additionalInitCode?.semanticAnalysisPhase1()?.let(reportings::addAll)
        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        check(selfVariableForAdditionalInitCode.semanticAnalysisPhase2().isEmpty())
        val reportings = mutableListOf<Reporting>()
        additionalInitCode?.semanticAnalysisPhase2()?.let(reportings::addAll)
        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        check(selfVariableForAdditionalInitCode.semanticAnalysisPhase3().isEmpty())
        val reportings = mutableListOf<Reporting>()
        additionalInitCode?.semanticAnalysisPhase3()?.let(reportings::addAll)
        return reportings
    }

    private val backendIr by lazy {
        val selfTemporary = IrCreateTemporaryValueImpl(IrAllocateObjectExpressionImpl(classDef))
        val initCode = ArrayList<IrExecutable>()
        initCode.add(selfTemporary)
        for (memberVariable in classDef.memberVariables) {
            val initialValue: IrExpression
            val initialValueIsRefcounted: Boolean
            if (memberVariable.isDefaultConstructorInitialized) {
                val parameter = parameters.parameters.single { it.name == memberVariable.name }
                initialValue = IrVariableAccessExpressionImpl(parameter.backendIrDeclaration)
                initialValueIsRefcounted = false
            } else {
                initialValue = memberVariable.initializer!!.toBackendIrExpression()
                initialValueIsRefcounted = memberVariable.initializer.isEvaluationResultReferenceCounted
            }
            val initialValueTemporary = IrCreateTemporaryValueImpl(initialValue)
            initCode.add(initialValueTemporary)
            initCode.add(IrAssignmentStatementImpl(
                IrAssignmentStatementTargetClassMemberVariableImpl(
                    memberVariable.toBackendIr(),
                    IrTemporaryValueReferenceImpl(selfTemporary),
                ),
                IrTemporaryValueReferenceImpl(initialValueTemporary),
            ))
            if (!initialValueIsRefcounted) {
                initCode.add(IrCreateReferenceStatementImpl(initialValueTemporary))
            } // else: the expression result value already accounts for the needed refcount-increment
        }

        if (additionalInitCode != null) {
            initCode.add(selfVariableForAdditionalInitCode.toBackendIrStatement())
            initCode.add(IrAssignmentStatementImpl(
                IrAssignmentStatementTargetVariableImpl(selfVariableForAdditionalInitCode.backendIrDeclaration),
                IrTemporaryValueReferenceImpl(selfTemporary),
            ))
            initCode.add(additionalInitCode.toBackendIrStatement())
        }

        IrDefaultConstructorImpl(
            this,
            IrCodeChunkImpl(listOfNotNull(
                IrCodeChunkImpl(initCode),
                IrReturnStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)),
            ))
        )
    }
    override fun toBackendIr(): IrFunction = backendIr
}

private class IrClassSimpleType(val classDef: BoundClassDefinition) : IrSimpleType {
    override val isNullable = false
    override val baseType get() = classDef.toBackendIr()
}

private class IrDefaultConstructorImpl(
    val ctor: BoundClassDefaultConstructor,
    override val body: IrCodeChunk,
) : IrImplementedFunction {
    override val fqn = ctor.classDef.fullyQualifiedName
    override val parameters = ctor.parameters.parameters.map { it.backendIrDeclaration }
    override val returnType = IrClassSimpleType(ctor.classDef)
    override val isExternalC = false
}

private class IrAllocateObjectExpressionImpl(val classDef: BoundClassDefinition) : IrAllocateObjectExpression {
    override val clazz: IrClass by lazy { classDef.toBackendIr() }
    override val evaluatesTo = object : IrSimpleType {
        override val isNullable = false
        override val baseType get() = this@IrAllocateObjectExpressionImpl.clazz
    }
}