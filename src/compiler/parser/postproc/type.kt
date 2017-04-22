/**
 *
 */
package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun TypePostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<TypeReference> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): TypeReference {
    val nameOrModifier = tokens.next()!!

    val typeModifier: TypeModifier?
    val nameToken: IdentifierToken

    if (nameOrModifier is TypeModifier) {
        typeModifier = nameOrModifier
        nameToken = tokens.next()!! as IdentifierToken
    }
    else {
        typeModifier = null
        nameToken = nameOrModifier as IdentifierToken
    }

    val isNullable = tokens.hasNext() && tokens.next()!! == OperatorToken(Operator.QUESTION_MARK)

    return TypeReference(nameToken, isNullable, typeModifier)
}


fun TypeModifierPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<TypeModifier> {
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