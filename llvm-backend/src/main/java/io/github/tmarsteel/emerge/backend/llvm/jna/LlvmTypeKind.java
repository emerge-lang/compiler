package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmTypeKind implements JnaEnum {
    VOID,
    HALF,
    FLOAT,
    DOUBLE,
    X86_FP80,
    FP128,
    PPC_FP128,
    LABEL,
    INTEGER,
    FUNCTION,
    STRUCT,
    ARRAY,
    POINTER,
    VECTOR,
    METADATA,
    X86_MMX,
    TOKEN,
    SCALABLE_VECTOR,
    BFLOAT,
    X86_AMX,
    TARGETEXT,
    ;

    public int intValue() {
        return ordinal();
    }
}
