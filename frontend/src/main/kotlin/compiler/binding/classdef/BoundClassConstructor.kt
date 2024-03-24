package compiler.binding.classdef

import compiler.InternalCompilerError
import compiler.ast.AssignmentStatement
import compiler.ast.ClassConstructorDeclaration
import compiler.ast.CodeChunk
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundVariable
import compiler.binding.IrAssignmentStatementImpl
import compiler.binding.IrAssignmentStatementTargetVariableImpl
import compiler.binding.IrCodeChunkImpl
import compiler.binding.IrReturnStatementImpl
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.reportings.Reporting
import compiler.reportings.ReportingException
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType

/**
 * The constructor of a class that, once compiled, does the basic bootstrapping:
 * 1. accept values for the constructor-initialized member variables
 * 2. allocate the appropriate amount of memory
 * 3. initialize all member variables as appropriate / as defined in their initializer expressions
 * 4. execute user-defined code additionally defined in a `constructor { ... }` block in the class definition
 */
class BoundClassConstructor(
    private val fileContext: CTContext,
    getClassDef: () -> BoundClassDefinition,
    val explicitDeclaration: ClassConstructorDeclaration?,
) : BoundFunction(), BoundClassEntry {
    val classDef: BoundClassDefinition by lazy(getClassDef)

    /*
    The contexts in a constructor:
    fileContext
      - constructorFunctionRootContext
        - contextWithSelfVar
            - contextWithParameters
     */
    private val constructorFunctionRootContext = MutableExecutionScopedCTContext.functionRootIn(fileContext)
    override val context = fileContext

    override val declaredAt get() = explicitDeclaration?.declaredAt ?: classDef.declaration.declaredAt
    override val receiverType = null
    override val declaresReceiver = false
    override val name get() = classDef.simpleName
    override val attributes = BoundFunctionAttributeList(explicitDeclaration?.attributes ?: emptyList())
    override val isPure = true
    override val isReadonly = true
    override val returnsExclusiveValue = true
    override val isGuaranteedToThrow = false
    override val typeParameters: List<BoundTypeParameter> by lazy {
        classDef.typeParameters.map { constructorFunctionRootContext.addTypeParameter(it.astNode) }
    }

    override val returnType by lazy {
        constructorFunctionRootContext.resolveType(
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
    }

    /*
    The contexts in a constructor:
    classRootContext
      - constructorFunctionRootContext
        - contextWithSelfVar
            - contextWithParameters
     */

    private val contextWithSelfVar = MutableExecutionScopedCTContext.deriveFrom(constructorFunctionRootContext)
    private val selfVariableForInitCode: BoundVariable by lazy {
        val varInstance = contextWithSelfVar.addVariable(VariableDeclaration(
            classDef.declaration.declaredAt,
            null,
            IdentifierToken("self"),
            (returnType as RootResolvedTypeReference).original!!.withMutability(TypeMutability.MUTABLE),
            null,
        ))
        contextWithSelfVar.markVariableInitialized(varInstance)
        varInstance
    }

    override val parameters by lazy {
        val astParameterList = ParameterList(classDef.memberVariables
            .filter { it.isConstructorParameterInitialized }
            .map { member ->
                VariableDeclaration(
                    member.declaration.declaredAt,
                    null,
                    member.declaration.name,
                    member.declaration.variableDeclaration.type!!.withMutability(member.type!!.mutability),
                    null,
                )
            })
        astParameterList.bindTo(contextWithSelfVar).also {
            it.semanticAnalysisPhase1()
        }
    }

    private val boundMemberVariableInitCodeFromCtorParams: BoundCodeChunk by lazy {
        classDef.memberVariables
            .filter { it.isConstructorParameterInitialized }
            .map { memberVariable ->
                val parameter = parameters.parameters.single { it.name == memberVariable.name }
                AssignmentStatement(
                    KeywordToken(Keyword.SET),
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(selfVariableForInitCode.name)),
                        OperatorToken(Operator.DOT),
                        IdentifierToken(memberVariable.name)
                    ),
                    OperatorToken(Operator.EQUALS),
                    IdentifierExpression(IdentifierToken(parameter.name)),
                )
            }
            .let(::CodeChunk)
            .bindTo(parameters.modifiedContext)
    }

    private val boundMemberVariableInitCodeFromExpression: BoundCodeChunk by lazy {
        classDef.memberVariables
            .filterNot { it.isConstructorParameterInitialized }
            .filter { it.initializer != null  /* if null, there should be another error diagnosed for it */ }
            .map { memberVariable ->
                AssignmentStatement(
                    KeywordToken(Keyword.SET),
                    MemberAccessExpression(
                        IdentifierExpression(IdentifierToken(selfVariableForInitCode.name)),
                        OperatorToken(Operator.DOT),
                        IdentifierToken(memberVariable.name)
                    ),
                    OperatorToken(Operator.EQUALS),
                    memberVariable.initializer!!.declaration,
                )
            }
            .let(::CodeChunk)
            .bindTo(parameters.modifiedContext)
    }

    private val additionalInitCode: BoundCodeChunk? = explicitDeclaration?.code?.bindTo(contextWithSelfVar)

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        // this has to be done first to make sure the type parameters are registered in the ctor function context
        typeParameters.map { it.semanticAnalysisPhase1() }.forEach(reportings::addAll)

        selfVariableForInitCode.semanticAnalysisPhase1().checkNoErrors()
        boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase1().checkNoErrors()

        reportings.addAll(boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase1())
        additionalInitCode?.semanticAnalysisPhase1()?.let(reportings::addAll)

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        typeParameters.map { it.semanticAnalysisPhase2() }.forEach(reportings::addAll)

        selfVariableForInitCode.semanticAnalysisPhase2().checkNoErrors()
        boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase2().checkNoErrors()

        reportings.addAll(boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase2())
        additionalInitCode?.semanticAnalysisPhase2()?.let(reportings::addAll)

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        typeParameters.map { it.semanticAnalysisPhase2() }.forEach(reportings::addAll)

        selfVariableForInitCode.semanticAnalysisPhase3().checkNoErrors()
        boundMemberVariableInitCodeFromCtorParams.semanticAnalysisPhase3().checkNoErrors()

        reportings.addAll(boundMemberVariableInitCodeFromExpression.semanticAnalysisPhase3())
        additionalInitCode?.semanticAnalysisPhase3()?.let(reportings::addAll)

        return reportings
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
        additionalInitCode?.toBackendIrStatement()?.let(initIr::add)

        IrDefaultConstructorImpl(
            this,
            IrCodeChunkImpl(listOfNotNull(
                IrCodeChunkImpl(initIr),
                IrReturnStatementImpl(IrTemporaryValueReferenceImpl(selfTemporary)),
            ))
        )
    }
    override fun toBackendIr(): IrImplementedFunction = backendIr
}

private class IrClassSimpleType(val classDef: BoundClassDefinition) : IrSimpleType {
    override val isNullable = false
    override val baseType get() = classDef.toBackendIr()
}

private class IrDefaultConstructorImpl(
    val ctor: BoundClassConstructor,
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

private fun Collection<Reporting>.checkNoErrors() {
    find { it.level >= Reporting.Level.ERROR }?.let {
        throw InternalCompilerError("Generated code has errors", ReportingException(it))
    }
}