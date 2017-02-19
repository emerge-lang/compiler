package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.types.TypeReference
import compiler.ast.VariableDeclaration
import compiler.ast.types.TypeModifier
import compiler.lexer.*
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun VariableDeclarationPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<VariableDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(input: TransactionalSequence<Any, Position>): VariableDeclaration {
    var modifierOrKeyword = input.next()!!

    val typeModifier: TypeModifier?
    val declarationKeyword: Keyword

    if (modifierOrKeyword is TypeModifier) {
        typeModifier = modifierOrKeyword
        declarationKeyword = (input.next()!! as KeywordToken).keyword
    }
    else {
        typeModifier = null
        declarationKeyword = (modifierOrKeyword as KeywordToken).keyword
    }

    val name = input.next()!! as IdentifierToken

    var type: TypeReference? = null

    var colonOrEqualsOrNewline = input.next()

    if (colonOrEqualsOrNewline == OperatorToken(Operator.COLON)) {
        type = input.next()!! as TypeReference
    }

    var assignExpression: Any? = null

    if (colonOrEqualsOrNewline == OperatorToken(Operator.EQUALS)) {
        // skip equals sign
        input.next()

        // assign expression, still todo
        colonOrEqualsOrNewline = input.next() ?: throw InternalCompilerError("Variable declaration with OPERATOR EQUALS but no assignment expression - this should have been a lexer error.")

        assignExpression = colonOrEqualsOrNewline

        if (type == null) {
            // type = InferredType(assignExpression)
            type = TypeReference(IdentifierToken("Inferred"), false)
        }
    }

    return VariableDeclaration(
        typeModifier,
        name,
        type,
        declarationKeyword == Keyword.VAR,
        assignExpression
    )
}