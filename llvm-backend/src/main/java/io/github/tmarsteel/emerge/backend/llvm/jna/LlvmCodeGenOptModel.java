package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmCodeGenOptModel implements JnaEnum {
    NONE,
    LESS,
    DEFAULT,
    AGGRESSIVE,
    ;

    public int getNumeric() {
        return ordinal();
    }
}
