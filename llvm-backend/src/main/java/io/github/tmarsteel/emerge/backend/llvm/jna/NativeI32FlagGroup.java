package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.FromNativeContext;
import com.sun.jna.ToNativeContext;
import org.jetbrains.annotations.NotNull;

/**
 * Models a 32-bit flag field, where each possible flag is represented by an enum entry in {@link T}.
 * @param <T> the enum type that holds the flag options
 */
public class NativeI32FlagGroup<T extends Enum<T> & NativeI32FlagGroup.FlagValue> {
    private int value;

    public void set(@NotNull T flag) {
        this.value |= flag.flagValue();
    }

    public void unset(@NotNull T flag) {
        this.value &= ~flag.flagValue();
    }

    public boolean isSet(@NotNull T flag) {
        return (this.value & flag.flagValue()) != 0;
    }

    public void clear() {
        this.value = 0;
    }

    interface FlagValue {
        /**
         * @return the bit representation of this value. Only one bit should be set.
         */
        int flagValue();
    }

    static class TypeConverter implements com.sun.jna.TypeConverter {
        @Override
        public Object fromNative(Object o, FromNativeContext fromNativeContext) {
            var flagGroup = new NativeI32FlagGroup();
            flagGroup.value = (Integer) o;
            return flagGroup;
        }

        @Override
        public Class<?> nativeType() {
            return int.class;
        }

        @Override
        public Object toNative(Object o, ToNativeContext toNativeContext) {
            return ((NativeI32FlagGroup<?>) o).value;
        }
    }
}
