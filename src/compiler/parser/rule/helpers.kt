package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.matching.SimpleMatchingResult

fun <T> successfulMatch(result: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): RuleMatchingResult<T>
        = SimpleMatchingResult(certainty, result)