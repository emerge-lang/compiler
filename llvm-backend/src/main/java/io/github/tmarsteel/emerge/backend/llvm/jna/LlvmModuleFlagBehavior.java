package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmModuleFlagBehavior implements JnaEnum {
    ERROR,
    WARNING,
    REQUIRE,
    OVERRIDE,
    APPEND,
    APPEND_UNIQUE,
    ;
}
