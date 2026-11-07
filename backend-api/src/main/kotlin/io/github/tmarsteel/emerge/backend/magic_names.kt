package io.github.tmarsteel.emerge.backend

/**
 * the function that implements the `expr[index]` syntax
 */
val GET_AT_INDEX_FN_NAME = "getAtIndex"

/**
 * the function that implements the `set expr[index] = value` syntax
 */
val SET_AT_INDEX_FN_NAME = "setAtIndex"

/**
 * the function that implements the `start..<endExclusive` syntax
 */
val RANGE_TO_EXCLUSIVE_FN_NAME = "rangeToExclusive"

/**
 * the function that implements the `expr[start..<endExclusive]` syntax
 */
val SLICE_FN_NAME = "slice"