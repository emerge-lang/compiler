package io.github.tmarsteel.emerge.backend.llvm.jna;

import javax.annotation.*;

public enum LlvmCodeModel implements JnaEnum {
    JIT_DEFAULT(null),
    TINY("tiny"),
    SMALL("small"),
    KERNEL("kernel"),
    MEDIUM("medium"),
    LARGE("large"),
    ;

    private final String llcName;

    LlvmCodeModel(String llcName) {
        this.llcName = llcName;
    }

    public @Nullable String getLlcName() {
        return llcName;
    }


    @Override
    public int intValue() {
        // DEFAULT is first
        return ordinal() + 1;
    }
}
