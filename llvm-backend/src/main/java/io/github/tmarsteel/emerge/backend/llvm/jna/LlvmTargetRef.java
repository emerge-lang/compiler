package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;

public class LlvmTargetRef extends PointerType {
    public LlvmTargetRef() {
    }

    public LlvmTargetRef(Pointer p) {
        super(p);
    }
}
