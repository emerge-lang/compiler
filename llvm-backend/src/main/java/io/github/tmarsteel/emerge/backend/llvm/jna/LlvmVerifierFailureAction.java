package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmVerifierFailureAction implements JnaEnum {
    /** will print the error to stderr and abort() */
    ABORT_PROCESS,
    /** will print the error to stderr and return 1 */
    PRINT_MESSAGE,
    /** will just return 1 */
    RETURN_STATUS,
    ;
}
