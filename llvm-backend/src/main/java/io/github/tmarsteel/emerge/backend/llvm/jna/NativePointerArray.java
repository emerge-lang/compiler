package io.github.tmarsteel.emerge.backend.llvm.jna;


import com.sun.jna.Memory;
import com.sun.jna.Native;
import com.sun.jna.Pointer;
import com.sun.jna.PointerType;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.lang.reflect.Array;
import java.lang.reflect.InvocationTargetException;
import java.util.Collection;
import java.util.ConcurrentModificationException;
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
            var pointerCtor = tClazz.getConstructor(Pointer.class);
            factory = (p) -> {
                try {
                    return (T) pointerCtor.newInstance(p);
                }
                catch (InstantiationException | IllegalAccessException | InvocationTargetException ex) {
                    throw new RuntimeException(ex);
                }
            };
        } catch (NoSuchMethodException ex) {
            try {
                var noArgsCtor = tClazz.getConstructor();
                factory = (p) -> {
                    T instance;
                    try {
                        instance = (T) noArgsCtor.newInstance();
                    }
                    catch (InstantiationException | IllegalAccessException | InvocationTargetException ex2) {
                        ex.addSuppressed(ex2);
                        throw new RuntimeException(ex);
                    }
                    instance.setPointer(p);
                    return instance;
                };
            }
            catch (NoSuchMethodException ex2) {
                ex.addSuppressed(ex2);
                throw new RuntimeException(ex);
            }
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
        if (size == 0) {
            return new NativePointerArray<>(null, null, 0, tClazz);
        }

        var block = new Memory(Native.POINTER_SIZE * (long) size);
        return new NativePointerArray<>(block, block, size, tClazz);
    }
}
