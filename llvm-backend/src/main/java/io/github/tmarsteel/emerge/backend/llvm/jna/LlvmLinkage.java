package io.github.tmarsteel.emerge.backend.llvm.jna;

public enum LlvmLinkage implements JnaEnum {
    /** Externally visible function  */
    EXTERNAL,
    AVAILABLE_EXTERNALLY,
    /** Keep one copy of function when linking (inline) */
    LINK_ONCE_ANY,
    /** Same, but only replaced by something equivalent.  */
    LINK_ONCE_ODR,
    /** Obsolete  */
    LINK_ONCE_ODR_AUTO_HIDE,
    /** Keep one copy of function when linking (weak)  */
    WEAK_ANY,
    /** Same, but only replaced by something equivalent.  */
    WEAK_ODR,
    /** Special purpose, only applies to global arrays  */
    APPENDING,
    /** Rename collisions when linking (static functions)  */
    INTERNAL,
    /** Like Internal, but omit from symbol table  */
    PRIVATE,
    /** Obsolete  */
    DLLIMPORT,
    /** Obsolete  */
    DLLEXPORT,
    /** External_Weak linkage description  */
    EXTERNAL_WEAK,
    /** Obsolete  */
    GHOST,
    /** Tentative definitions  */
    COMMON,
    /** Like Private, but linker removes.  */
    LINKER_PRIVATE,
    /** Like {@link #LINKER_PRIVATE}, but is weak.  */
    LINKER_PRIVATE_WEAK,
    ;

    @Override
    public int intValue() {
        return ordinal();
    }
}
