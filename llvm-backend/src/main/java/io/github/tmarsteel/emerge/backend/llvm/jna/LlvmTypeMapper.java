package io.github.tmarsteel.emerge.backend.llvm.jna;

import com.sun.jna.*;

public class LlvmTypeMapper extends DefaultTypeMapper {
    public LlvmTypeMapper() {
        addTypeConverter(JnaEnum.class, new JnaEnum.TypeConverter());
    }
}
