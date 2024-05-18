package compiler.binding

/**
 * Describes what is known about the occurrence of a particular side effect (e.g. return, throw) at runtime.
 * A `null` value of this type means: analysis hasn't been done yet, the runtime behavior is completely unknown.
 */
enum class SideEffectPrediction {
    /** the side effect will never occur */
    NEVER,

    /** the side effect may occur at runtime, not necessarily though */
    POSSIBLY,

    /** the side effect is guaranteed to occur at runtime */
    GUARANTEED,
    ;

    companion object {
        /**
         * @return the [SideEffectPrediction] when sequentially executing code with `this` and [other] behavior.
         */
        fun SideEffectPrediction?.combineSequentialExecution(other: SideEffectPrediction?): SideEffectPrediction? = when (this) {
            null -> when (other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
                null -> null
            }
            NEVER -> when (other) {
                NEVER -> NEVER
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
                null -> POSSIBLY
            }
            POSSIBLY -> when(other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
                null -> POSSIBLY
            }
            GUARANTEED -> GUARANTEED
        }

        /**
         * @return the [SideEffectPrediction] when sequentially executing code with `this` behaviors; an empty
         * collection will result in [NEVER].
         */
        fun Iterable<SideEffectPrediction?>.reduceSequentialExecution(): SideEffectPrediction? {
            val iterator = iterator()
            if (!iterator.hasNext()) {
                return NEVER
            }

            var carry = iterator.next()
            while (iterator.hasNext()) {
                carry = carry.combineSequentialExecution(iterator.next())
                if (carry == GUARANTEED) {
                    break
                }
            }

            return carry
        }

        /**
         * @return the [SideEffectPrediction] when executing code with **either** `this` **or** [other]
         * behavior, depending on a runtime value (used for conditions, loops).
         */
        fun SideEffectPrediction?.combineBranch(other: SideEffectPrediction?): SideEffectPrediction? = when (this) {
            null -> null
            NEVER -> when (other) {
                NEVER -> NEVER
                POSSIBLY -> POSSIBLY
                GUARANTEED -> POSSIBLY
                null -> null
            }
            POSSIBLY -> when (other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> POSSIBLY
                null -> null
            }
            GUARANTEED -> when(other) {
                NEVER -> POSSIBLY
                POSSIBLY -> POSSIBLY
                GUARANTEED -> GUARANTEED
                null -> null
            }
        }
    }
}