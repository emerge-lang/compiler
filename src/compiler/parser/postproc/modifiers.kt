package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.type.FunctionModifier
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.Rule

fun FunctionModifierPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<FunctionModifier> {
    return rule
        .flatten()
        .mapResult { tokens -> when((tokens.next()!! as KeywordToken).keyword) {
            Keyword.READONLY -> FunctionModifier.READONLY
            Keyword.NOTHROW  -> FunctionModifier.NOTHROW
            Keyword.PURE     -> FunctionModifier.PURE
            Keyword.OPERATOR -> FunctionModifier.OPERATOR
            Keyword.EXTERNAL -> FunctionModifier.EXTERNAL
            else             -> throw InternalCompilerError("Keyword is not a function modifier")
        }}
}