package compiler.matching

enum class ResultCertainty(val level: Int) {
    /**
     * The input did not match at least one unique part of the pattern.
     */
    NOT_RECOGNIZED(10),

    /**
     * At least one unique property of the pattern was fulfilled by the input
     */
    MATCHED(15),

    /**
     * All unique properties of the pattern were fulfilled by the input; however, errors were still encountered.
     */
    OPTIMISTIC(20),

    /**
     * The input did fulfill all requirements.
     */
    DEFINITIVE(25)
}