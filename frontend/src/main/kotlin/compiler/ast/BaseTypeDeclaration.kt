package compiler.ast

import compiler.InternalCompilerError
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundParameterList
import compiler.binding.BoundStatement
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundBaseTypeMemberVariableAttributes
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import compiler.binding.basetype.BoundDeclaredBaseTypeMemberFunction
import compiler.binding.basetype.BoundSupertypeList
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeParameter.Companion.chain
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.entryNotAllowedOnBaseType
import compiler.diagnostic.multipleClassConstructors
import compiler.diagnostic.multipleClassDestructors
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import compiler.util.partitionIsInstanceOf
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants

class BaseTypeDeclaration(
    val declarationKeyword: KeywordToken,
    val visibility: AstVisibility?,
    val name: IdentifierToken,
    val supertype: TypeReference?,
    val entryDeclarations: List<BaseTypeEntryDeclaration>,
    val typeParameters: List<TypeParameter>?,
) : AstFileLevelDeclaration {
    override val declaredAt = name.span

    fun bindTo(fileContext: CTContext): BoundBaseType {
        /*
        this method is SERIOUSLY complex, because it does all the reordering of the syntactic elements in the
        base type definition, including a bunch of code generation for the constructor
         */

        val bindTimeDiagnosis = CollectingDiagnosis()

        // declare this now to allow passing forward references to all children
        // TODO: maybe no longer needed after BoundBaseType.init has been added
        lateinit var boundTypeDef: BoundBaseType
        val typeDefAccessor = { boundTypeDef }

        val canonicalName = CanonicalElementName.BaseType(fileContext.packageName, name.value)
        val kind = when (declarationKeyword.keyword) {
            Keyword.CLASS_DEFINITION -> BoundBaseType.Kind.CLASS
            Keyword.INTERFACE_DEFINITION -> BoundBaseType.Kind.INTERFACE
            else -> throw InternalCompilerError("Unknown base type declaration keyword ${declarationKeyword.span}")
        }
        val typeVisibility = visibility?.bindTo(fileContext) ?: BoundVisibility.default(fileContext)
        val (boundTypeParameters, fileContextWithDeclaredTypeParams) = typeParameters?.chain(fileContext) ?: Pair(null, fileContext)
        val typeRootContext = MutableCTContext(fileContextWithDeclaredTypeParams, typeVisibility)
        val boundSupertypeList = BoundSupertypeList.bindSingleSupertype(supertype, typeRootContext, typeDefAccessor)
        val buildAstReceiverType: (Span) -> AstAbsoluteTypeReference = { span ->
            AstAbsoluteTypeReference(
                canonicalName,
                typeParameters?.map { astTypeParam ->
                    AstSpecificTypeArgument(TypeVariance.UNSPECIFIED, NamedTypeReference(astTypeParam.name.value, span = span))
                },
                span = span,
            )
        }

        val givenConstructorDeclarations = entryDeclarations.filterIsInstance<BaseTypeConstructorDeclaration>()
        val chosenConstructorDeclaration = givenConstructorDeclarations.firstOrNull()
            ?: BaseTypeConstructorDeclaration.generateDefault(this)
        val superfluousConstructorDeclarations = givenConstructorDeclarations.drop(1)

        val (memberVariableEntryDecls, nonVarEntryDecls) = entryDeclarations.partitionIsInstanceOf<_, BaseTypeMemberVariableDeclaration>()
        val (boundChosenCtor, boundMemberVars) = chosenConstructorDeclaration.bindConstructorAndMemberVariables(
            fileContextWithDeclaredTypeParams,
            boundTypeParameters ?: emptyList(),
            typeRootContext,
            memberVariableEntryDecls,
            buildAstReceiverType,
            typeDefAccessor,
        )

        boundTypeDef = BoundBaseType(
            fileContext = fileContext,
            typeRootContext = typeRootContext,
            kind = kind,
            visibility = typeVisibility,
            typeParameters = boundTypeParameters,
            superTypes = boundSupertypeList,
            declaration = this,
            bindTimeDiagnosis = bindTimeDiagnosis,
        )

        val boundNonVarEntries = nonVarEntryDecls
            .asSequence()
            .filter { it !is BaseTypeConstructorDeclaration } // they are irrelevant here
            .map { entry ->
                when (entry) {
                    is BaseTypeMemberFunctionDeclaration -> {
                        entry.bindTo(
                            typeRootContext,
                            buildAstReceiverType(entry.functionDeclaration.parameters.parameters.firstOrNull()?.name?.span ?: entry.span),
                            typeDefAccessor
                        )
                    }
                    is BaseTypeDestructorDeclaration -> {
                        entry.bindTo(fileContext, fileContextWithDeclaredTypeParams, boundTypeParameters, typeDefAccessor)
                    }
                    is BaseTypeMemberVariableDeclaration,
                    is BaseTypeConstructorDeclaration -> error("unreachable, member vars and constructors are done above")
                }
            }
            .toList()

        boundTypeDef.init(boundChosenCtor, boundMemberVars, boundNonVarEntries)

        if (kind.hasCtorsAndDtors) {
            if (superfluousConstructorDeclarations.isNotEmpty()) {
                bindTimeDiagnosis.multipleClassConstructors(superfluousConstructorDeclarations)
            }
            entryDeclarations
                .asSequence()
                .filterIsInstance<BaseTypeDestructorDeclaration>()
                .drop(1)
                .toList()
                .takeIf { it.isNotEmpty() }
                ?.let {
                    bindTimeDiagnosis.multipleClassDestructors(it)
                }
        } else {
            entryDeclarations
                .asSequence()
                .filter { it is BaseTypeConstructorDeclaration || it is BaseTypeDestructorDeclaration }
                .forEach {
                    bindTimeDiagnosis.entryNotAllowedOnBaseType(boundTypeDef, it)
                }
        }

        return boundTypeDef
    }
}

sealed interface BaseTypeEntryDeclaration {
    val span: Span
}

sealed class BaseTypeMemberDeclaration : BaseTypeEntryDeclaration {
    abstract val name: IdentifierToken
}

class BaseTypeMemberVariableDeclaration(
    val attributes: List<KeywordToken>,
    val variableDeclaration: VariableDeclaration,
) : BaseTypeMemberDeclaration() {
    override val span = variableDeclaration.declaredAt
    override val name = variableDeclaration.name

    val isConstructorParameterInitialized = if (variableDeclaration.initializerExpression is IdentifierExpression) {
        variableDeclaration.initializerExpression.identifier.value == EmergeConstants.MAGIC_IDENTIFIER_CONSTRUCTOR_INITIALIZED_MEMBER_VARIABLE
    } else {
        false
    }

    val isDecorated = attributes.any { it.keyword == Keyword.DECORATES }

    inner class Binder(val typeRootContext: CTContext) {
        val isConstructorParameterInitialized: Boolean = this@BaseTypeMemberVariableDeclaration.isConstructorParameterInitialized
        val isDecorated: Boolean = this@BaseTypeMemberVariableDeclaration.isDecorated

        private var needsCtorTypeParameter: Boolean? = if (!isDecorated || !isConstructorParameterInitialized) false else null
        private var ctorTypeParameter: BoundTypeParameter? = null

        fun generateTypeParameterForConstructor(
            contextBeforeCtorFunctionRoot: CTContext,
            referenceToTypeParameterForDecoratorMutability: BoundTypeReference,
        ): BoundTypeParameter? {
            if (needsCtorTypeParameter == false) {
                return null
            }
            val declaredType = variableDeclaration.type
            val isGenericOnBaseType = declaredType is NamedTypeReference && typeRootContext.resolveTypeParameter(declaredType.simpleName) != null
            if (isGenericOnBaseType) {
                // already generic, there's no point to further parameterize this one
                needsCtorTypeParameter = false
                return null
            }
            val declaredTypeOrAny = declaredType ?: AstAbsoluteTypeReference(typeRootContext.swCtx.any.canonicalName, span = variableDeclaration.declaredAt)

            val typeParamBound = declaredTypeOrAny.intersect(referenceToTypeParameterForDecoratorMutability.asAstReference())
            ctorTypeParameter = BoundTypeParameter(
                TypeParameter(
                    TypeVariance.UNSPECIFIED,
                    IdentifierToken(contextBeforeCtorFunctionRoot.findInternalTypeParameterName(variableDeclaration.name.value), span.deriveGenerated()),
                    typeParamBound,
                    span = span.deriveGenerated(),
                ),
                contextBeforeCtorFunctionRoot,
            )
            return ctorTypeParameter
        }

        private var ctorParam: BoundVariable? = null
        /**
         * if this member variable needs a constructor parameter, returns a suitable one
         */
        fun generateConstructorParameter(
            contextInCtor: ExecutionScopedCTContext,
            span: Span,
        ): BoundVariable? {
            check(needsCtorTypeParameter != null) { "call ${this::generateTypeParameterForConstructor.name} first" }

            if (!isConstructorParameterInitialized) {
                return null
            }

            val astNode = variableDeclaration.copy(
                initializerExpression = null,
                visibility = null,
                type = if (needsCtorTypeParameter!!) {
                    NamedTypeReference(IdentifierToken(ctorTypeParameter!!.name, span))
                } else {
                    variableDeclaration.type
                        ?: AstAbsoluteTypeReference(typeRootContext.swCtx.any.canonicalName, span = span)
                },
            )
            ctorParam = astNode.bindToAsConstructorParameter(contextInCtor)
            return ctorParam
        }

        private var boundLocalVariableInCtor: BoundVariable? = null
        fun generateConstructorInitializationCode(
            contextInCtor: ExecutionScopedCTContext,
            selfVariable: BoundVariable,
        ): List<BoundStatement<*>> {
            val generatedSourceLocation = variableDeclaration.initializerExpression?.span ?: variableDeclaration.span
            val valueForAssignment: Expression
            val contextForAssignment: ExecutionScopedCTContext
            when {
                isConstructorParameterInitialized -> {
                    check(ctorParam != null) { "call ${this::generateConstructorParameter.name} first" }
                    contextForAssignment = contextInCtor
                    valueForAssignment = IdentifierExpression(IdentifierToken(ctorParam!!.name, generatedSourceLocation))
                }
                variableDeclaration.initializerExpression != null -> {
                    boundLocalVariableInCtor = variableDeclaration.copy(visibility = null).bindTo(contextInCtor)
                    contextForAssignment = boundLocalVariableInCtor!!.modifiedContext
                    valueForAssignment = IdentifierExpression(variableDeclaration.name)
                }
                else -> return emptyList() // nothing to do
            }

            val assignmentAstNode = AssignmentStatement(
                KeywordToken(Keyword.SET, span = generatedSourceLocation),
                MemberAccessExpression(
                    IdentifierExpression(IdentifierToken(selfVariable.name, generatedSourceLocation)),
                    OperatorToken(Operator.DOT, generatedSourceLocation),
                    IdentifierToken(variableDeclaration.name.value, generatedSourceLocation),
                ),
                OperatorToken(Operator.EQUALS, generatedSourceLocation),
                valueForAssignment,
                considerSettersOnMemberVariableAssignment = false,
            )

            return listOfNotNull(boundLocalVariableInCtor) + listOf(assignmentAstNode.bindTo(contextForAssignment))
        }

        private lateinit var boundVar: BoundBaseTypeMemberVariable
        fun bindMemberVariableFinal(getTypeDef: () -> BoundBaseType): BoundBaseTypeMemberVariable {
            if (!this::boundVar.isInitialized) {
                boundVar = BoundBaseTypeMemberVariable(
                    typeRootContext,
                    boundLocalVariableInCtor,
                    variableDeclaration.visibility?.bindTo(typeRootContext)
                        ?: BoundVisibility.default(typeRootContext),
                    BoundBaseTypeMemberVariableAttributes(attributes),
                    getTypeDef,
                    this@BaseTypeMemberVariableDeclaration,
                )
            }

            return boundVar
        }
    }
}

class BaseTypeConstructorDeclaration(
    val attributes: List<AstFunctionAttribute>,
    val constructorKeyword: KeywordToken,
    val code: AstCodeChunk,
) : BaseTypeEntryDeclaration {
    override val span = constructorKeyword.span

    fun bindConstructorAndMemberVariables(
        fileContextWithDeclaredTypeParams: CTContext,
        boundTypeParameters: List<BoundTypeParameter>,
        typeRootContext: CTContext,
        memberVarDecls: List<BaseTypeMemberVariableDeclaration>,
        buildReceiverType: (Span) -> AstAbsoluteTypeReference,
        typeDefAccessor: () -> BoundBaseType,
    ): Pair<BoundClassConstructor, List<BoundBaseTypeMemberVariable>> {
        val ctorGeneratedSpan = span.deriveGenerated()
        val memberVariableBinders = memberVarDecls.map { it.Binder(typeRootContext) }

        val typeParameterForDecoratorMutability: BoundTypeParameter?
        val additionalTypeParamsForDecoratedMembers = mutableListOf<BoundTypeParameter>()
        val typeRootContextWithAllCtorTypeParameters: CTContext
        if (memberVariableBinders.any { it.isDecorated }) {
            typeParameterForDecoratorMutability = BoundTypeParameter(
                TypeParameter(
                    TypeVariance.UNSPECIFIED,
                    IdentifierToken(typeRootContext.findInternalTypeParameterName("M"), ctorGeneratedSpan),
                    null,
                    ctorGeneratedSpan,
                ),
                typeRootContext,
            )
            val refToTypeParameterForDecoratorMutability = GenericTypeReference(
                NamedTypeReference(IdentifierToken(typeParameterForDecoratorMutability.name, ctorGeneratedSpan)),
                typeParameterForDecoratorMutability
            )
            var contextCarry = typeParameterForDecoratorMutability.modifiedContext
            for (binder in memberVariableBinders) {
                val typeParam = binder.generateTypeParameterForConstructor(contextCarry, refToTypeParameterForDecoratorMutability)
                    ?: continue
                contextCarry = typeParam.modifiedContext
                additionalTypeParamsForDecoratedMembers.add(typeParam)
            }
            typeRootContextWithAllCtorTypeParameters = contextCarry
        } else {
            typeParameterForDecoratorMutability = null
            typeRootContextWithAllCtorTypeParameters = typeRootContext
        }

        val constructorFunctionRootContext = BoundClassConstructor.ConstructorRootContext(typeRootContextWithAllCtorTypeParameters, typeDefAccessor)
        val selfVariableForInitCode = VariableDeclaration(
            declaredAt = ctorGeneratedSpan,
            visibility = null,
            varToken = null,
            ownership = null,
            name = IdentifierToken(BoundParameterList.RECEIVER_PARAMETER_NAME, ctorGeneratedSpan),
            type = buildReceiverType(ctorGeneratedSpan).withMutability(TypeMutability.EXCLUSIVE),
            initializerExpression = null,
        ).bindTo(constructorFunctionRootContext)
        selfVariableForInitCode.defaultOwnership = VariableOwnership.BORROWED
        var constructorContextWithAllArguments: ExecutionScopedCTContext = MutableExecutionScopedCTContext.deriveNewScopeFrom(selfVariableForInitCode.modifiedContext)
        val constructorParameters = mutableListOf<BoundVariable>()
        for (binder in memberVariableBinders) {
            val boundParam = binder.generateConstructorParameter(constructorContextWithAllArguments, ctorGeneratedSpan)
                ?: continue
            constructorParameters.add(boundParam)
            constructorContextWithAllArguments = boundParam.modifiedContext
        }
        val constructorContextForInitCode = MutableExecutionScopedCTContext.deriveFrom(constructorContextWithAllArguments)

        val memberVariableInitCode = mutableListOf<BoundStatement<*>>()
        for (binder in memberVariableBinders.filter { it.isConstructorParameterInitialized }) {
            memberVariableInitCode.addAll(
                binder
                    .generateConstructorInitializationCode(
                        memberVariableInitCode.lastOrNull()?.modifiedContext ?: constructorContextForInitCode,
                        selfVariableForInitCode
                    )
            )
        }
        val boundConstructorInitCode = BoundCodeChunk.fromBoundStatements(
            memberVariableInitCode,
            constructorContextForInitCode,
        )

        // the context with the ctor params is not continued here so the user-defined init code can't see them and has to
        // access them through the selfVariableForInitCode
        val contextForUserInitCode = MutableExecutionScopedCTContext.deriveFrom(selfVariableForInitCode.modifiedContext)
        val userInitCode = mutableListOf<BoundStatement<*>>()
        for ((index, binder) in memberVariableBinders.filter { !it.isConstructorParameterInitialized }.withIndex()) {
            userInitCode.addAll(
                binder
                    .generateConstructorInitializationCode(
                        userInitCode.lastOrNull()?.modifiedContext ?: contextForUserInitCode,
                        selfVariableForInitCode
                    )
            )
        }

        val boundMemberVariables = memberVariableBinders
            .map { it.bindMemberVariableFinal(typeDefAccessor) }
            .toList()

        userInitCode.add(code.bindTo(userInitCode.lastOrNull()?.modifiedContext ?: contextForUserInitCode))
        val boundBody = BoundCodeChunk.fromBoundStatements(
            userInitCode,
            contextForUserInitCode,
        )
        val boundCtor = BoundClassConstructor(
            fileContextWithDeclaredTypeParams,
            constructorFunctionRootContext,
            boundTypeParameters ?: emptyList(),
            typeParameterForDecoratorMutability,
            additionalTypeParamsForDecoratedMembers,
            BoundParameterList(
                constructorFunctionRootContext,
                ParameterList(constructorParameters.map { it.declaration }),
                constructorParameters,
            ),
            selfVariableForInitCode,
            constructorContextForInitCode,
            boundConstructorInitCode,
            contextForUserInitCode,
            boundBody,
            this,
            buildReceiverType,
            typeDefAccessor,
        )

        return Pair(boundCtor, boundMemberVariables)
    }

    companion object {
        fun generateDefault(forBaseType: BaseTypeDeclaration): BaseTypeConstructorDeclaration {
            val span = forBaseType.declaredAt.deriveGenerated()
            return BaseTypeConstructorDeclaration(
                listOfNotNull(forBaseType.visibility),
                KeywordToken(Keyword.CONSTRUCTOR, span = span),
                AstCodeChunk(emptyList(), span),
            )
        }
    }
}

class BaseTypeDestructorDeclaration(
    val destructorKeyword: KeywordToken,
    val attributes: List<AstFunctionAttribute>,
    val code: AstCodeChunk,
) : BaseTypeEntryDeclaration {
    override val span = destructorKeyword.span

    fun bindTo(
        parentContext: CTContext,
        parentContextWithTypeParameters: CTContext,
        typeParameters: List<BoundTypeParameter>?,
        getClassDef: () -> BoundBaseType
    ): BoundClassDestructor {
        lateinit var dtor: BoundClassDestructor
        dtor = BoundClassDestructor(
            parentContext,
            parentContextWithTypeParameters,
            typeParameters ?: emptyList(),
            getClassDef,
            BoundFunctionAttributeList(parentContextWithTypeParameters, { dtor }, attributes),
            this
        )
        return dtor
    }
}

class BaseTypeMemberFunctionDeclaration(
    val functionDeclaration: FunctionDeclaration
) : BaseTypeMemberDeclaration() {
    override val span = functionDeclaration.declaredAt
    override val name = functionDeclaration.name

    fun bindTo(
        typeRootContext: CTContext,
        receiverType: AstAbsoluteTypeReference,
        getTypeDef: () -> BoundBaseType,
    ): BoundDeclaredBaseTypeMemberFunction {
        return functionDeclaration.bindToAsMember(
            this,
            typeRootContext,
            receiverType,
            getTypeDef,
        )
    }
}