package compiler.ast

import compiler.ast.expression.BooleanLiteralExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.NullLiteralExpression
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants

/**
 * The code the compiler adds to a `unique class`: a variable that knows whether the one instance of
 * the class was handed out already, and the static function `take` that hands it out.
 *
 * The variable is a global variable of the file, private to it. Its name starts with
 * [EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX]; code other than the code generated here must not refer
 * to it.
 */
class UniqueClassCode(
    private val classDeclaration: BaseTypeDeclaration,
    private val classCanonicalName: CanonicalElementName.BaseType,
    private val constructorDeclaration: BaseTypeConstructorDeclaration,
) {
    private val span: Span = classDeclaration.uniqueKeyword!!.span.deriveGenerated()
    private val flagName = "${EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX}${classDeclaration.name.value}_taken"

    val flagVariable = VariableDeclaration(
        declaredAt = span,
        annotations = AstAnnotationSet.EMPTY,
        visibility = AstVisibility.Private(KeywordToken(Keyword.PRIVATE, span = span)),
        varToken = KeywordToken(Keyword.VAR, span = span),
        ownership = null,
        name = IdentifierToken(flagName, span),
        type = AstAbsoluteTypeReference(
            CanonicalElementName.BaseType(EmergeConstants.CoreModule.NAME, "Bool"),
            span = span,
        ),
        initializerExpression = BooleanLiteralExpression(span, false),
    )

    /**
     * ```
     * mut fn take(world: mut World, <constructor parameters>) -> own C? {
     *     if taken { return null }
     *     instance = C(<constructor parameters>)
     *     if taken { return null } // the constructor obtained the instance itself
     *     set taken = true
     *     return instance
     * }
     * ```
     */
    val takeFunction: BaseTypeMemberFunctionDeclaration by lazy {
        val constructorParameters = classDeclaration.entryDeclarations
            .filterIsInstance<BaseTypeMemberVariableDeclaration>()
            .filter { it.isConstructorParameterInitialized }
            .map { it.variableDeclaration }
        val namesInUse = constructorParameters.map { it.name.value }.toSet()
        fun unusedName(base: String): String = generateSequence(base) { it + "_" }.first { it !in namesInUse }

        val worldParameter = VariableDeclaration(
            declaredAt = span,
            annotations = AstAnnotationSet.EMPTY,
            visibility = null,
            varToken = null,
            ownership = null,
            name = IdentifierToken(unusedName("world"), span),
            type = AstAbsoluteTypeReference(EmergeConstants.PlatformModule.WORLD_TYPE_NAME, mutability = TypeMutability.MUTABLE, span = span),
            initializerExpression = null,
        )
        val forwardedParameters = constructorParameters.map {
            it.copy(
                declaredAt = span,
                annotations = AstAnnotationSet.EMPTY,
                visibility = null,
                varToken = null,
                ownership = Pair(VariableOwnership.CAPTURED, KeywordToken(Keyword.CAPTURE, span = span)),
                type = it.type ?: AstAbsoluteTypeReference(ANY_TYPE_NAME, span = span),
                initializerExpression = null,
            )
        }

        fun flag() = IdentifierExpression(IdentifierToken(flagName, span))
        fun returnNullIfTaken() = IfExpression(
            span,
            KeywordToken(Keyword.IF, span = span),
            flag(),
            AstCodeChunk(listOf(ReturnExpression(KeywordToken(Keyword.RETURN, span = span), NullLiteralExpression(span))), span),
            null,
        )
        val instanceName = unusedName("instance")
        val body = AstCodeChunk(
            listOf(
                returnNullIfTaken(),
                VariableDeclaration(
                    declaredAt = span,
                    annotations = AstAnnotationSet.EMPTY,
                    visibility = null,
                    varToken = null,
                    ownership = null,
                    name = IdentifierToken(instanceName, span),
                    type = AstAbsoluteTypeReference(classCanonicalName, mutability = TypeMutability.OWN, span = span),
                    initializerExpression = InvocationExpression(
                        IdentifierExpression(IdentifierToken(classDeclaration.name.value, span)),
                        null,
                        forwardedParameters.map { IdentifierExpression(IdentifierToken(it.name.value, span)) },
                        span,
                    ),
                ),
                returnNullIfTaken(),
                AssignmentStatement(
                    KeywordToken(Keyword.SET, span = span),
                    flag(),
                    OperatorToken(Operator.ASSIGNMENT, span),
                    BooleanLiteralExpression(span, true),
                ),
                ReturnExpression(
                    KeywordToken(Keyword.RETURN, span = span),
                    IdentifierExpression(IdentifierToken(instanceName, span)),
                ),
            ),
            span,
        )

        BaseTypeMemberFunctionDeclaration(FunctionDeclaration(
            annotations = AstAnnotationSet.EMPTY,
            declarationKeyword = KeywordToken(Keyword.FUNCTION, span = span),
            attributes = constructorDeclaration.attributes.filterIsInstance<AstVisibility>() + listOf(
                AstFunctionAttribute.EffectCategory(BoundFunction.Purity.MODIFYING, KeywordToken(Keyword.MUTABLE, span = span)),
            ),
            name = IdentifierToken(EmergeConstants.UNIQUE_CLASS_TAKE_FUNCTION_NAME, span),
            typeParameters = emptyList(),
            parameters = ParameterList(listOf(worldParameter) + forwardedParameters),
            parsedReturnType = AstAbsoluteTypeReference(
                classCanonicalName,
                nullability = TypeReference.Nullability.NULLABLE,
                mutability = TypeMutability.OWN,
                span = span,
            ),
            body = FunctionDeclaration.Body.Full(body),
        ))
    }

    companion object {
        private val ANY_TYPE_NAME = CanonicalElementName.BaseType(EmergeConstants.CoreModule.NAME, "Any")
    }
}
