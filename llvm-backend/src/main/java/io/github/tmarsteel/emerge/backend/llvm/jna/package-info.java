/**
 * contains JNA mappings for the LLVM 17 C interface. This is minimal mapping, staying as close to the underlying C API
 * as much as possible, because the C interface uses weakly typed pointers that cannot be type-checked at runtime. E.g.
 * a {@link io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef} can be an instruction, a function reference or a
 * temporary value. JVM code cannot, at runtime, do an instanceof check on these (requires C++ ABI knowledge). So best
 * to keep this straight and honest, and do additional type-safety in a parallel JVM-based type hierarchy.
 */
package io.github.tmarsteel.emerge.backend.llvm.jna;