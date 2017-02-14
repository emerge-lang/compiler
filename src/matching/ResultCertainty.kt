package matching

enum class ResultCertainty(val level: Int) {
    /**
     * Least certainty, alias Nice-To-Have
     */
    OPTIMISTIC(10),

    /**
     * The result is definitive, no more rules should be matched
     */
    DEFINITIVE(10)
}