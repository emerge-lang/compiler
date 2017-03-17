package compiler.matching

/**
 * Matching certainty. **The order of declaration is important!**
 */
enum class ResultCertainty : Comparable<ResultCertainty> {
    /**
     * The input did not match at least one unique part of the pattern.
     */
    NOT_RECOGNIZED,

    /**
     * At least one unique property of the pattern was fulfilled by the input
     */
    MATCHED,

    /**
     * All unique properties of the pattern were fulfilled by the input; however, errors were still encountered.
     */
    OPTIMISTIC,

    /**
     * The input did fulfill all requirements.
     */
    DEFINITIVE
}