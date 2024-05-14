package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmRelocMode implements JnaEnum {
    DEFAULT("default"),
    /** Non-relocatable code */
    STATIC("static"),
    /** Fully relocatable, position independent code */
    POSITION_INDEPENDENT("pic"),
    /** Relocatable external references, non-relocatable code **/
    RELOCATABLE_EXTERNAL_REFERENCES("dynamic-no-pic"),
    /** Code and read-only data relocatable, accessed PC-relative */
    ROPI("ropi"),
    /** Read-write data relocatable, accessed relative to static base */
    RWPI("rwpi"),
    /** Combination of ropi and rwpi */
    ROPI_RWPI("ropi-rwpi"),
    ;

    private final String llcName;

    LlvmRelocMode(String llcName) {
        this.llcName = llcName;
    }

    public String getLlcName() {
        return llcName;
    }
}
