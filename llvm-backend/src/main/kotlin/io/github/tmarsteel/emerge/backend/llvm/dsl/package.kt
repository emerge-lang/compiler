/**
 * A small DSL for LLVM. Its supposed to make writing LLVM here simpler,
 * easier (re. memory management) and also more robust (because we can reference things
 * by name, instead of through indices in getelementptr instructions)
 */
package io.github.tmarsteel.emerge.backend.llvm.dsl
