package compiler.ast

enum class VariableOwnership {
    BORROWED,
    CAPTURED,
    ;

    /**
     * Given a parameter is declared with `this` ownership and overrides a parameter with [superValue],
     * ownership.
     * @return  whether the override is legal
     */
    fun canOverride(superValue: VariableOwnership): Boolean = when (this) {
        BORROWED -> true
        CAPTURED -> superValue == CAPTURED
    }
}