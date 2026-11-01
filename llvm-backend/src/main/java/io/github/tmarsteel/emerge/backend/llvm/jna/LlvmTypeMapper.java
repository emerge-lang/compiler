package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.DefaultTypeMapper;

public class LlvmTypeMapper extends DefaultTypeMapper {
    public LlvmTypeMapper() {
        addTypeConverter(JnaEnum.class, new JnaEnum.TypeConverter());
        addTypeConverter(NativeI32FlagGroup.class, new NativeI32FlagGroup.TypeConverter());
    }
}
