package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmIntPredicate implements JnaEnum {
    EQUAL(32),
    NOT_EQUAL(33),
    UNSIGNED_GREATER_THAN(34),
    UNSIGNED_GREATER_THAN_OR_EQUAL(35),
    UNSIGNED_LESS_THAN(36),
    UNSIGNED_LESS_THAN_OR_EQUAL(37),
    SIGNED_GREATER_THAN(38),
    SIGNED_GREATER_THAN_OR_EQUAL(39),
    SIGNED_LESS_THAN(40),
    SIGNED_LESS_THAN_OR_EQUAL(41),
    ;

    private final int intValue;

    LlvmIntPredicate(int intValue) {
        this.intValue = intValue;
    }

    @Override
    public int intValue() {
        return intValue;
    }
}