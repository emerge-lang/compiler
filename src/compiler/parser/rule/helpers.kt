package compiler.parser.rule

import compiler.matching.ResultCertainty

fun <T> successfulMatch(result: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): MatchingResult<T>
        = SimpleMatchingResult(certainty, result)