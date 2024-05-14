package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;

import java.util.*;

/**
 * thanks to http://technofovea.com/blog/archives/815
 */
public interface JnaEnum {
    default int intValue() {
        return ((Enum<?>) this).ordinal();
    }

    static class TypeConverter implements com.sun.jna.TypeConverter {
        @SuppressWarnings("unchecked")
        @Override
        public Object fromNative(Object nativeValue, FromNativeContext context) {
            int intValue = (Integer) nativeValue;
            Class<?> targetClass = context.getTargetType();
            if (!targetClass.isEnum()) {
                throw new RuntimeException("Cannot convert to " + targetClass.getName() + " as an enum; it is not a java enum");
            }
            if (!JnaEnum.class.isAssignableFrom(targetClass)) {
                throw new RuntimeException("Cannot convert to " + targetClass.getName() + " as an enum; it does not implement " + JnaEnum.class.getName());
            }

            return Arrays.stream(((Class<? extends JnaEnum>) targetClass).getEnumConstants())
                    .filter(c -> c.intValue() == intValue)
                    .findFirst()
                    .orElseThrow(() -> new RuntimeException("Unknown enum value " + intValue + " for enum " + targetClass.getName()));
        }

        @Override
        public Class<?> nativeType() {
            return int.class;
        }

        @Override
        public Object toNative(Object value, ToNativeContext context) {
            return ((JnaEnum) value).intValue();
        }


    }
}