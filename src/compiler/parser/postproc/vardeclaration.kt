package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.TypeReference
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
    val typeModifier = input.next()!! as TypeModifier

    val declarationKeyword = (input.next()!! as KeywordToken).keyword

    val name = input.next()!! as IdentifierToken

    var type: TypeReference? = null

    var next = input.next()

    if (next == OperatorToken(Operator.COLON)) {
        type = input.next()!! as TypeReference

        input.next()
    }

    var assignExpression: Any? = null

    if (input.hasNext()) {
        // skip equals sign
        input.next()

        // assign expression, still todo
        next = input.next() ?: throw InternalCompilerError("Variable declaration with OPERATOR EQUALS but no assignment expression - this should have been a lexer error.")

        assignExpression = next

        if (type == null) {
            // type = InferredType(assignExpression)
            type = TypeReference(IdentifierToken("Inferred"), false)
        }
    }

    return VariableDeclaration(
        name,
        type?.modifiedWith(typeModifier),
        declarationKeyword == Keyword.VAR,
        assignExpression
    )
}