package io.github.tmarsteel.emerge.backend.llvm.dsl

/**
 * Generates unique names. One instance per scope where LLVM will want unique names. E.g.
 * * all globals in a module
 * * temporary values in a function
 */
class NameScope(private val prefix: String) {
    private var counter: ULong = 0u

    fun next(): String {
        return "$prefix${counter++}"
    }
}