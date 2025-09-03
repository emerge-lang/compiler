package io.github.tmarsteel.emerge.backend.llvm.jna;

/**
 * see <a href="https://dwarfstd.org/doc/DWARF4.pdf">DWARF v4 Spec</a>, Page 77, Figure 13.
 */
public enum DwarfBaseTypeEncoding implements JnaEnum {
    ADDRESS(0x01),
    BOOLEAN(0x02),
    COMPLEX_FLOAT(0x03),
    FLOAT(0x04),
    SIGNED(0x05),
    SIGNED_CHAR(0x06),
    UNSIGNED(0x07),
    UNSIGNED_CHAR(0x08),
    IMAGINARY_FLOAT(0x09),
    PACKED_DECIMAL(0x0A),
    NUMERIC_STRING(0x0B),
    EDITED(0x0C),
    SIGNED_FIXED(0x0D),
    UNSIGNED_FIXED(0x0E),
    DECIMAL_FLOAT(0x0F),
    UTF(0x10),
    UCS(0x11),
    ASCII(0x12),
    LO_USER(0x80),
    HI_USER(0xFF),
    ;

    private final int intValue;

    DwarfBaseTypeEncoding(int intValue) {
        this.intValue = intValue;
    }

    @Override
    public int intValue() {
        return this.intValue;
    }
}
