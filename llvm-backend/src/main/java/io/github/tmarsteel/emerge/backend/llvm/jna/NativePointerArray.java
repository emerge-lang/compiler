package io.github.tmarsteel.emerge.backend.llvm.jna;


import com.sun.jna.*;
import org.jetbrains.annotations.*;

import java.lang.reflect.*;
import java.util.*;
import java.util.function.Function;

public class NativePointerArray<T extends PointerType> extends PointerType implements AutoCloseable {
    @Nullable
    private final Memory deallocateOnClose;
    private final int length;

    private final Class<?> tClazz;

    public NativePointerArray() {
        deallocateOnClose = null;
        length = 0;
        tClazz = Object.class;
    }

    private NativePointerArray(Memory deallocateOnClose, Pointer pointerToFirstElement, int length, Class<?> tClazz) {
        super(pointerToFirstElement);
        this.deallocateOnClose = deallocateOnClose;
        this.length = length;
        this.tClazz = tClazz;
    }

    public int getLength() {
        return length;
    }

    @SuppressWarnings("unchecked")
    public @NotNull T[] copyToJava() {
        Function<Pointer, T> factory = getComponentTypeFactory();
        var rawPointers = this.getPointer().getPointerArray(0, length);
        T[] javaStorage;
        try {
            javaStorage = (T[]) Array.newInstance(tClazz, length);
        } catch (SecurityException ex) {
            throw new RuntimeException(ex);
        }
        for (int i = 0;i < length;i++) {
            var pointer = rawPointers[i];
            if (pointer == null) {
                javaStorage[i] = null;
            } else {
                factory.apply(pointer);
            }
        }

        return javaStorage;
    }

    @NotNull
    @SuppressWarnings("unchecked")
    private Function<Pointer, T> getComponentTypeFactory() {
        Function<Pointer, T> factory;
        try {
            var ctor = tClazz.getConstructor(Pointer.class);
            factory = (p) -> {
                try {
                    return (T) ctor.newInstance(p);
                }
                catch (InstantiationException | IllegalAccessException | InvocationTargetException ex) {
                    throw new RuntimeException(ex);
                }
            };
        } catch (NoSuchMethodException ex) {
            throw new RuntimeException(ex);
        }
        return factory;
    }

    @Override
    public void close() throws Exception {
        if (deallocateOnClose != null) {
            deallocateOnClose.close();
        }
    }

    public static <T extends PointerType> @NotNull NativePointerArray<T> fromJavaPointers(@NotNull Collection<T> javaPointers) {
        if (javaPointers.isEmpty()) {
            return new NativePointerArray<T>(
                    null,
                    null,
                    0,
                    Pointer.class
            );
        }

        var length = javaPointers.size();
        var block = new Memory((long) Native.POINTER_SIZE * (long) length);
        var iterator = javaPointers.iterator();
        int i = 0;
        for (;i < length;i++) {
            var pointerHolder = iterator.next();
            if (pointerHolder == null) {
                block.setPointer((long) i * Native.POINTER_SIZE, null);
            } else {
                block.setPointer((long) i * Native.POINTER_SIZE, pointerHolder.getPointer());
            }
        }
        if (i != length) {
            throw new ConcurrentModificationException("Collection size changed during iteration");
        }
        Class tClazz = javaPointers.stream().findFirst().map(e -> (Class) e.getClass()).orElse(Pointer.class);
        return new NativePointerArray<>(block, block, length, tClazz);
    }

    public static <T extends PointerType> @NotNull NativePointerArray<T> allocate(int size, Class<T> tClazz) {
        var block = new Memory(Native.POINTER_SIZE * (long) size);
        return new NativePointerArray<>(block, block, size, tClazz);
    }
}
