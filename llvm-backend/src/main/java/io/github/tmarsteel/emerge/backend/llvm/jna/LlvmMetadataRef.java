package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.PointerType;
import org.jetbrains.annotations.NotNull;

public class LlvmMetadataRef extends PointerType {
    public @NotNull LlvmMetadataKind getKind() {
        return Llvm.LLVMGetMetadataKind(this);
    }
}
