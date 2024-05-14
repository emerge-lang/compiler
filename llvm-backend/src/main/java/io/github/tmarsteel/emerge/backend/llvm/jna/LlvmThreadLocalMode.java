package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmThreadLocalMode implements JnaEnum {
    NOT_THREAD_LOCAL,
    GENERAL_DYNAMIC,
    LOCAL_DYNAMIC,
    INITIAL_EXEC,
    LOCAL_EXEC,
    ;

    @Override
    public int intValue() {
        return ordinal();
    }
}
