package io.github.tmarsteel.emerge.backend.llvm.linux_x86_64

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.SystemPropertyDelegate.Companion.systemProperty
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM
import java.nio.channels.AsynchronousFileChannel
import java.nio.file.Path
import java.nio.file.Paths
import java.nio.file.StandardOpenOption

class Linux_x68_64_Backend : EmergeBackend {
    override val targetName = "linux-x86_64"

    override val targetSpecificModules: Collection<ModuleSourceRef> = setOf(
        ModuleSourceRef(FFI_C_SOURCES_PATH, DotName(listOf("emerge", "ffi", "c"))),
        ModuleSourceRef(LINUX_LIBC_SOURCES_PATH, DotName(listOf("emerge", "linux", "libc"))),
        ModuleSourceRef(LINUX_PLATFORM_PATH, DotName(listOf("emerge", "platform"))),
    )

    override fun emit(softwareContext: IrSoftwareContext, directory: Path) {
        LLVM.LLVMInitializeX86Target()
        LLVM.LLVMInitializeX86TargetInfo()

        LlvmContext("x86_64-pc-linux-unknown").use { llvmContext ->
            softwareContext.packagesSeq.forEach { pkg ->
                pkg.structs.forEach(llvmContext::registerStruct)
            }
            softwareContext.modules.flatMap { it.packages }.forEach { pkg ->
                pkg.functions.flatMap { it.overloads }.forEach { function ->
                    val functionType = LLVM.LLVMFunctionType(
                        llvmContext.getType(function.returnType),
                        PointerPointer(*function.parameters.map { llvmContext.getType(it.type) }.toTypedArray()),
                        function.parameters.size,
                        0,
                    )
                    LLVM.LLVMAddFunction(llvmContext.module, function.llvmName, functionType)
                }
            }
            LLVM.LLVMDumpModule(llvmContext.module)
            LLVM.LLVMPrintModuleToString(llvmContext.module).let { moduleBytes ->
                AsynchronousFileChannel.open(directory.resolve("out.bin"), StandardOpenOption.CREATE, StandardOpenOption.WRITE).use {
                    it.write(moduleBytes.asBuffer(), 0L).get()
                }
                LLVM.LLVMDisposeMessage(moduleBytes)
            }
        }
    }

    companion object {
        val FFI_C_SOURCES_PATH by systemProperty("emerge.compiler.native.c-ffi-sources", Paths::get)
        val LINUX_LIBC_SOURCES_PATH by systemProperty("emerge.compiler.native.libc-wrapper.sources", Paths::get)
        val LINUX_PLATFORM_PATH by systemProperty("emerge.compiler.native.linux-platform.sources", Paths::get)
    }
}

private val IrFunction.llvmName: String get() = this.fqn.toString()
private val IrStruct.llvmName: String get() = this.fqn.toString()

private val IrSoftwareContext.packagesSeq: Sequence<IrPackage> get() = modules.asSequence()
    .flatMap { it.packages }

private class LlvmContext(val targetTriple: String) : AutoCloseable {
    private val ref = LLVM.LLVMContextCreate()
    val module = LLVM.LLVMModuleCreateWithName("app")
    init {
        LLVM.LLVMSetTarget(module, targetTriple)
    }
    private val targetData = LLVM.LLVMGetModuleDataLayout(module)
    private val intType = LLVM.LLVMInt32TypeInContext(ref)
    private val pointerType = LLVM.LLVMPointerTypeInContext(ref, 0)
    private val wordType = LLVM.LLVMIntTypeInContext(ref, LLVM.LLVMPointerSize(targetData) * 8)
    private val voidType = LLVM.LLVMVoidType()

    private val baseTypeRefs = HashMap<IrBaseType, LLVMTypeRef>()
    fun registerStruct(struct: IrStruct) {
        if (struct in baseTypeRefs) {
            return
        }

        val structType = LLVM.LLVMStructCreateNamed(ref, struct.llvmName)
        // register here to allow cyclic references
        baseTypeRefs[struct] = structType
        val elements = PointerPointer(*struct.members.map { getType(it.type) }.toTypedArray())
        LLVM.LLVMStructSetBody(structType, elements, struct.members.size, 0)
    }

    fun getType(type: IrType): LLVMTypeRef {
        val baseType: IrBaseType = when (type) {
            is IrSimpleType -> type.baseType
            is IrParameterizedType -> type.simpleType.baseType
            is IrGenericTypeReference -> return getType(type.effectiveBound)
        }

        when (baseType.fqn.toString()) {
            "emerge.ffi.c.COpaquePointer",
            "emerge.ffi.c.CPointer" -> return pointerType
            "emerge.core.Int" -> return intType
            "emerge.core.Array" -> return pointerType
            "emerge.core.iword",
            "emerge.core.uword" -> return wordType
            "emerge.core.Unit" -> return voidType
            "emerge.core.Any" -> return pointerType // TODO: remove, Any will be a pure language-defined type
        }

        return baseTypeRefs[baseType] ?: throw CodeGenerationException("Unknown base type $baseType")
    }

    override fun close() {
        LLVM.LLVMDisposeModule(module)
        LLVM.LLVMContextDispose(ref)
    }
}

private fun <T : Any> iterateLinkedList(
    first: T?,
    next: (T) -> T?
): Sequence<T> = sequence {
    var pivot = first
    while (pivot != null) {
        yield(pivot)
        pivot = next(pivot)
    }
}
private fun <K, V> MutableMap<K, V>.dropAllAndDo(action: (Map.Entry<K, V>) -> Unit) {
    val iterator = iterator()
    while (iterator.hasNext()) {
        val next = iterator.next()
        iterator.remove()
        action(next)
    }
}