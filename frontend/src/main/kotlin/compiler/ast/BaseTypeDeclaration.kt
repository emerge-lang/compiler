package compiler.ast

import compiler.InternalCompilerError
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.AstAbsoluteTypeReference
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
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
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

        boundTypeDef = BoundBaseType(
            fileContext = fileContext,
            fileContextWithDeclaredTypeParams,
            typeRootContext = typeRootContext,
            kind = kind,
            visibility = typeVisibility,
            typeParameters = boundTypeParameters,
            superTypes = boundSupertypeList,
            declaration = this,
        )

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
    val attributes: BoundBaseTypeMemberVariableAttributes,
    val variableDeclaration: VariableDeclaration,
) : BaseTypeMemberDeclaration() {
    override val span = variableDeclaration.declaredAt
    override val name = variableDeclaration.name

    val isConstructorParameterInitialized = if (variableDeclaration.initializerExpression is IdentifierExpression) {
        variableDeclaration.initializerExpression.identifier.value == EmergeConstants.MAGIC_IDENTIFIER_CONSTRUCTOR_INITIALIZED_MEMBER_VARIABLE
    } else {
        false
    }

    inner class Binder(val typeRootContext: CTContext) {
        val isConstructorParameterInitialized: Boolean = this@BaseTypeMemberVariableDeclaration.isConstructorParameterInitialized

        private val isOwned: Boolean = attributes.ownership == BoundBaseTypeMemberVariable.Ownership.OWNED
        private var needsCtorTypeParameter: Boolean? = if (isConstructorParameterInitialized && isOwned) null /* not yet known*/ else false /* definitely not */
        private var ctorTypeParameter: BoundTypeParameter? = null
        val mayNeedConstructorTypeParameter: Boolean get()= needsCtorTypeParameter != false
        private val resolvedType: BoundTypeReference? by lazy {
            variableDeclaration.type?.let(typeRootContext::resolveType)
        }
        private val isMutabilityTiedToParentObject: Boolean get() = isOwned && resolvedType?.mutability in setOf(null, TypeMutability.top())

        fun generateTypeParameterForConstructor(
            contextBeforeCtorFunctionRoot: CTContext,
            referenceToTypeParameterForDecoratorMutability: BoundTypeReference,
        ): BoundTypeParameter? {
            if (needsCtorTypeParameter == false) {
                return null
            }
            val declaredType = variableDeclaration.type

            // TODO: is this special case necessary? it may even be incorrect
            // if this is removed, the Binder can be simplified significantly by making needsCtorTypeParameter non-nullable
            val isGenericOnBaseType = declaredType is NamedTypeReference && typeRootContext.resolveTypeParameter(declaredType.simpleName) != null
            if (isGenericOnBaseType) {
                // already generic, there's no point to further parameterize this one
                needsCtorTypeParameter = false
                return null
            }
            if (resolvedType?.mutability !in setOf(null, TypeMutability.top())) {
                // mutability is pre-determined, no need to parameterize the constructor
                needsCtorTypeParameter = false
                return null
            }
            needsCtorTypeParameter = true

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
                    boundLocalVariableInCtor = variableDeclaration.copy(visibility = null).bindToAsLocalVariable(
                        context = contextInCtor,
                        typeInferenceStrategy = if (isConstructorParameterInitialized && isMutabilityTiedToParentObject) {
                            BoundVariable.TypeInferenceStrategy.OwnedMemberVariable
                        } else {
                            BoundVariable.TypeInferenceStrategy.InferBaseTypeAndMutability
                        }
                    )
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
        fun bindMemberVariableFinal(baseType: BoundBaseType): BoundBaseTypeMemberVariable {
            if (!this::boundVar.isInitialized) {
                boundVar = BoundBaseTypeMemberVariable(
                    typeRootContext,
                    boundLocalVariableInCtor,
                    variableDeclaration.visibility?.bindTo(typeRootContext)
                        ?: BoundVisibility.default(typeRootContext),
                    attributes,
                    baseType,
                    this@BaseTypeMemberVariableDeclaration,
                    isMutabilityTiedToParentObject,
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

    private fun createDecorationCtorTypeParameters(
        typeRootContext: CTContext,
        memberVariableBinders: List<BaseTypeMemberVariableDeclaration.Binder>,
        ctorGeneratedSpan: Span,
    ): Triple<List<BoundTypeParameter>, BoundTypeParameter?, CTContext> {
        if (memberVariableBinders.none { it.mayNeedConstructorTypeParameter }) {
            return Triple(emptyList(), null, typeRootContext)
        }

        val additionalTypeParamsForDecoratedMembers = mutableListOf<BoundTypeParameter>()
        val typeParameterForDecoratorMutability = BoundTypeParameter(
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

        if (additionalTypeParamsForDecoratedMembers.isEmpty()) {
            return Triple(additionalTypeParamsForDecoratedMembers, null, typeRootContext)
        } else {
            return Triple(additionalTypeParamsForDecoratedMembers, typeParameterForDecoratorMutability, contextCarry)
        }
    }

    fun bindConstructorAndMemberVariables(
        fileContextWithDeclaredTypeParams: CTContext,
        boundTypeParameters: List<BoundTypeParameter>,
        typeRootContext: CTContext,
        memberVarDecls: List<BaseTypeMemberVariableDeclaration>,
        buildReceiverType: (Span) -> AstAbsoluteTypeReference,
        baseType: BoundBaseType,
    ): Pair<BoundClassConstructor, List<BoundBaseTypeMemberVariable>> {
        val ctorGeneratedSpan = span.deriveGenerated()
        val memberVariableBinders = memberVarDecls.map { it.Binder(typeRootContext) }

        val (additionalTypeParamsForDecoratedMembers, typeParameterForDecoratorMutability, typeRootContextWithAllCtorTypeParameters) = createDecorationCtorTypeParameters(
            typeRootContext,
            memberVariableBinders,
            ctorGeneratedSpan,
        )
        val constructorFunctionRootContext = BoundClassConstructor.ConstructorRootContext(typeRootContextWithAllCtorTypeParameters, baseType)
        val selfVariableForInitCode = VariableDeclaration(
            declaredAt = ctorGeneratedSpan,
            visibility = null,
            varToken = null,
            ownership = null,
            name = IdentifierToken(BoundParameterList.RECEIVER_PARAMETER_NAME, ctorGeneratedSpan),
            type = buildReceiverType(ctorGeneratedSpan).withMutability(TypeMutability.top()),
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
        memberVariableBinders
            .asSequence()
            .filter { it.isConstructorParameterInitialized }
            .forEach { binder ->
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
        memberVariableBinders
            .asSequence()
            .filter { !it.isConstructorParameterInitialized }
            .forEach { binder ->
                userInitCode.addAll(
                    binder
                        .generateConstructorInitializationCode(
                            userInitCode.lastOrNull()?.modifiedContext ?: contextForUserInitCode,
                            selfVariableForInitCode
                        )
                )
            }

        val boundMemberVariables = memberVariableBinders
            .map { it.bindMemberVariableFinal(baseType) }
            .toList()

        userInitCode.add(code.bindTo(userInitCode.lastOrNull()?.modifiedContext ?: contextForUserInitCode))
        val boundBody = BoundCodeChunk.fromBoundStatements(
            userInitCode,
            contextForUserInitCode,
        )
        val boundCtor = BoundClassConstructor(
            fileContextWithDeclaredTypeParams,
            constructorFunctionRootContext,
            boundTypeParameters,
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
            baseType,
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
        baseType: BoundBaseType
    ): BoundClassDestructor {
        lateinit var dtor: BoundClassDestructor
        dtor = BoundClassDestructor(
            parentContext,
            parentContextWithTypeParameters,
            typeParameters ?: emptyList(),
            baseType,
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
        baseType: BoundBaseType,
    ): BoundDeclaredBaseTypeMemberFunction {
        return functionDeclaration.bindToAsMember(
            this,
            typeRootContext,
            receiverType,
            baseType,
        )
    }
}