/**
 *
 */
package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.TypeReference
import compiler.ast.types.TypeModifier
import compiler.lexer.*
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun TypePostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<TypeReference> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): TypeReference {
    val nameToken = tokens.next()!! as IdentifierToken

    val isNullable = tokens.hasNext() && tokens.next()!! == OperatorToken(Operator.QUESTION_MARK)

    return TypeReference(nameToken, isNullable)
}


fun TypeModifierPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<TypeModifier> {
    return rule
        .flatten()
        .mapResult { tokens ->
            val keyword = (tokens.next() as KeywordToken?)?.keyword
            when(keyword) {
                Keyword.MUTABLE   -> TypeModifier.MUTABLE
                Keyword.READONLY  -> TypeModifier.READONLY
                Keyword.IMMUTABLE -> TypeModifier.IMMUTABLE
                null -> TypeModifier.MUTABLE
                else -> throw InternalCompilerError("Keyword ${keyword.text} is not a type modifier")
            }
        }
}