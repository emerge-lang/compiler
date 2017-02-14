package parser.rule

import matching.ResultCertainty

fun <T> successfulMatch(result: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): MatchingResult<T>
        = SimpleMatchingResult(certainty, result)