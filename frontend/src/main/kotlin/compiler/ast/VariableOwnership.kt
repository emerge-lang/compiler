package compiler.ast

import compiler.lexer.Keyword

enum class VariableOwnership(val keyword: Keyword) {
    BORROWED(Keyword.BORROW),
    CAPTURED(Keyword.CAPTURE),
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