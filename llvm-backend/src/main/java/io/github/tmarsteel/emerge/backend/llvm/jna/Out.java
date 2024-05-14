package io.github.tmarsteel.emerge.backend.llvm.jna;

import java.lang.annotation.*;

/**
 * The parameter annotated with this annotation is an output of the function. The type of that
 * parameter should be a {@link com.sun.jna.ptr.ByReference}.
 */
@Retention(RetentionPolicy.SOURCE)
@Target(ElementType.PARAMETER)
public @interface Out {
}
