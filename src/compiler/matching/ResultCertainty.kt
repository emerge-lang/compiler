package compiler.matching

enum class ResultCertainty(val level: Int) {
    /**
     * Least certainty
     */
    OPTIMISTIC(10),

    /**
     * The result is definitive, no more rules should be matched
     */
    DEFINITIVE(20)
}