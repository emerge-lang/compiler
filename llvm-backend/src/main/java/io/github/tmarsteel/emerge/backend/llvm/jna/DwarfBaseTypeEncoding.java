package io.github.tmarsteel.emerge.backend.llvm.jna;

/**
 * see <a href="https://dwarfstd.org/doc/DWARF4.pdf">DWARF v4 Spec</a>, Page 77, Figure 13.
 */
public enum DwarfBaseTypeEncoding implements JnaEnum {
    ADDRESS,
    BOOLEAN,
    COMPLEX_FLOAT,
    FLOAT,
    SIGNED,
    SIGNED_CHAR,
    UNSIGNED,
    UNSIGNED_CHAR,
    IMAGINARY_FLOAT,
    PACKED_DECIMAL,
    NUMERIC_STRING,
    EDITED,
    SIGNED_FIXED,
    UNSIGNED_FIXED,
    DECIMAL_FLOAT,
    UTF;
}
