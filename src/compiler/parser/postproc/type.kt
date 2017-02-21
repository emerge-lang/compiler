/**
 *
 */
package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeModifier
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
    val nameOrModifier = tokens.next()!!

    val typeModifier: TypeModifier
    val nameToken: IdentifierToken

    if (nameOrModifier is TypeModifier) {
        typeModifier = nameOrModifier
        nameToken = tokens.next()!! as IdentifierToken
    }
    else {
        typeModifier = TypeModifier.MUTABLE
        nameToken = nameOrModifier as IdentifierToken
    }

    val isNullable = tokens.hasNext() && tokens.next()!! == OperatorToken(Operator.QUESTION_MARK)

    return TypeReference(nameToken, isNullable, typeModifier)
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
                else -> throw InternalCompilerError("$keyword is not a type modifier")
            }
        }
}