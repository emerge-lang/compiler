package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;

public class LlvmTypeRef extends PointerType {
    public LlvmTypeRef() {
        super();
    }

    public LlvmTypeRef(Pointer p) {
        super(p);
    }
}