package io.github.tmarsteel.emerge.backend.llvm.jna;

import java.lang.annotation.*;

/**
 * A parameter annotated with this annotation must contain the size of an array pointed to by another parameter.
 */
@Target(ElementType.PARAMETER)
@Retention(RetentionPolicy.SOURCE)
@Unsigned
public @interface ArraySizeOf {
    /** name of the parameter that is the pointer to the first array element */
    String value();
}
