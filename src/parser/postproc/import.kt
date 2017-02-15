/**
 *
 */
package parser.postproc

import lexer.Operator
import lexer.OperatorToken
import parser.Reporting
import parser.TokenMismatchReporting
import parser.rule.MatchingResult
import parser.rule.Rule

val ImportPostprocessor = { rule: Rule<List<MatchingResult<*>>> ->
    rule
    // enhance error for "import xyz"
    .enhanceErrors(
        { it is TokenMismatchReporting && it.expected == OperatorToken(Operator.DOT) && it.actual == OperatorToken(Operator.NEWLINE) },
        { _it ->
            val it = _it as TokenMismatchReporting
            Reporting.Companion.error("${it.message}; To import all exports of the module write module.*", it.actual)
        }
    )
}