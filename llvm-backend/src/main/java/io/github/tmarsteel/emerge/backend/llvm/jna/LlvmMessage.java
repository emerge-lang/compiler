package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;

public class LlvmMessage extends PointerType {

    private String value;

    public LlvmMessage() {
    }

    @Override
    public Object fromNative(Object nativeValue, FromNativeContext context) {
        var ptr = (Pointer) nativeValue;
        if (ptr == null) {
            return null;
        }
        var holder = new LlvmMessage();
        holder.value = ptr.getString(0);
        Llvm.LLVMDisposeMessage(ptr);
        return holder;
    }

    @Override
    public Object toNative() {
        throw new UnsupportedOperationException();
    }

    public String getValue() {
        return value;
    }

    @Override
    public String toString() {
        return value;
    }
}
