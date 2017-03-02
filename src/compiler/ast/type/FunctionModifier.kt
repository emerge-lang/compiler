package compiler.ast.type

/** Function modifiers */
enum class FunctionModifier {
    /**
     * The function may only read from its enclosing context and only invoke other functions that are marked with
     * [READONLY] or that don't actually read from their enclosing context.
     */
    READONLY,

    /**
     * The function may not throw exceptions nor may it call other functions that throw exceptions.
     */
    NOTHROW,

    /**
     * The function must not interact with its enclosing scope nor may it call other functions that do. That
     * assures that the function is deterministic and allows for aggressive optimization using CTFE.
     */
    PURE,

    /**
     * The function defines or overrides an operator.
     */
    OPERATOR,

    /**
     * The functions body is provided to the compiler by other means than source language code.
     *
     * For example, a lot of the builtin types use this modifier in their defining statements. At compile time the
     * compiler loads the function body appropriate for the compile target.
     */
    EXTERNAL
}