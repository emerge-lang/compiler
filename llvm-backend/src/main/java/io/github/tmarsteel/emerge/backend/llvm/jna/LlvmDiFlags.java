package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmDiFlags implements NativeI32FlagGroup.FlagValue {
    PRIVATE(1),
    PROTECTED(2),
    PUBLIC(3),
    FORWARD_DECLARATION(1 << 2),
    APPLE_BLOCK(1 << 3),
    VIRTUAL(1 << 5),
    ARTIFICIAL(1 << 6),
    EXPLICIT(1 << 7),
    PROTOTYPED(1 << 8),
    OBJECTIVE_C_CLASSCOMPLETE(1 << 9),
    OBJECT_POINTER(1 << 10),
    VECTOR(1 << 11),
    STATIC_MEMBER(1 << 12),
    LVALUEREFERENCE(1 << 13),
    RVALUEREFERENCE(1 << 14),
    SINGLE_INHERITANCE(1 << 16),
    MULTIPLE_INHERITANCE(2 << 16),
    VIRTUAL_INHERITANCE(3 << 16),
    INTRODUCED_VIRTUAL(1 << 18),
    BITFIELD(1 << 19),
    NORETURN(1 << 20),
    TYPE_PASS_BY_VALUE(1 << 22),
    TYPE_PASS_BY_REFERENCE(1 << 23),
    ENUM_CLASS(1 << 24),
    THUNK(1 << 25),
    NONTRIVIAL(1 << 26),
    BIG_ENDIAN(1 << 27),
    LITTLE_ENDIAN(1 << 28),
    INDIRECT_VIRTUAL_BASE((1 << 2) | (1 << 5)),
    ACCESSIBILITY(PRIVATE.flagValue() | PROTECTED.flagValue() | PUBLIC.flagValue()),
    POINTER_TO_MEMBER_REP(SINGLE_INHERITANCE.flagValue() | MULTIPLE_INHERITANCE.flagValue() | VIRTUAL_INHERITANCE.flagValue()),
    ;

    private final int flagValue;

    LlvmDiFlags(int flagValue) {
        this.flagValue = flagValue;
    }

    public int flagValue() {
        return this.flagValue;
    }
}