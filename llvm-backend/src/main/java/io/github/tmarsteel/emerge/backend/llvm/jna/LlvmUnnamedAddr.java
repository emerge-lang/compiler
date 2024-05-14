package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmUnnamedAddr implements JnaEnum {
    NO_UNNAMED_ADDR,
    LOCAL_UNNAMED_ADDR,
    GLOBAL_UNNAMED_ADDR,
    ;

    @Override
    public int intValue() {
        return ordinal();
    }
}