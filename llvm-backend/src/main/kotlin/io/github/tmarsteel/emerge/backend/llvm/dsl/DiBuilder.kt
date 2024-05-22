package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfEmissionKind
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfSourceLanguage
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmModuleRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.nio.file.Path

class DiBuilder(
    moduleRef: LlvmModuleRef,
    filePath: Path,
    emissionKind: LlvmDwarfEmissionKind = LlvmDwarfEmissionKind.Full,
    forProfiling: Boolean = false,
) : AutoCloseable {
    private val ref = Llvm.LLVMCreateDIBuilder(moduleRef)
    private val contextRef = Llvm.LLVMGetModuleContext(moduleRef)

    val file: DebugInfoScope.File
    val compileUnit: DebugInfoScope.CompileUnit

    init {
        val dirBytes = (filePath.parent?.toString() ?: "").toByteArray(Charsets.UTF_8)
        val filenameBytes = filePath.fileName.toString().toByteArray(Charsets.UTF_8)
        val fileRef = Llvm.LLVMDIBuilderCreateFile(
            ref,
            filenameBytes,
            NativeLong(filenameBytes.size.toLong()),
            dirBytes,
            NativeLong(dirBytes.size.toLong()),
        )
        file = DebugInfoScope.File(fileRef)

        val compileUnitRef = Llvm.LLVMDIBuilderCreateCompileUnit(
            ref,
            LlvmDwarfSourceLanguage.C,
            fileRef,
            PRODUCER, NativeLong(PRODUCER.size.toLong()),
            0,
            null, ZERO_WORD,
            0,
            null, ZERO_WORD,
            emissionKind,
            0,
            1,
            if (forProfiling) 1 else 0,
            null, ZERO_WORD,
            null, ZERO_WORD,
        )
        compileUnit = DebugInfoScope.CompileUnit(compileUnitRef)
    }

    fun createFunction(
        name: CanonicalElementName.Function,
        onLineNumber: UInt
    ): DebugInfoScope.Function {
        check(!closed)

        val type = NativePointerArray.allocate(0, LlvmMetadataRef::class.java).use { parameterTypesArray ->
            Llvm.LLVMDIBuilderCreateSubroutineType(
                ref,
                file.ref,
                parameterTypesArray,
                parameterTypesArray.length,
                0,
            )
        }

        val nameBytes = name.toString().toByteArray(Charsets.UTF_8)
        val ref = Llvm.LLVMDIBuilderCreateFunction(
            ref,
            compileUnit.ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            null, ZERO_WORD,
            file.ref,
            onLineNumber.toInt(),
            type,
            1, // TODO: defer from visibility
            1,
            0,
            0,
            0,
        )

        return DebugInfoScope.Function(ref)
    }

    fun createDebugLocation(
        scope: DebugInfoScope,
        line: UInt,
        column: UInt,
    ): LlvmMetadataRef {
        check(!closed)

        return Llvm.LLVMDIBuilderCreateDebugLocation(
            contextRef,
            line.toInt(),
            column.toInt(),
            scope.ref,
            null,
        )
    }

    private var finalized = false
    fun diFinalize() {
        if (finalized) {
            return
        }
        finalized = true
        Llvm.LLVMDIBuilderFinalize(ref)
    }

    private var closed = false
    override fun close() {
        if (closed) {
            return
        }
        closed = true

        diFinalize()
        Llvm.LLVMDisposeDIBuilder(ref)
    }

    companion object {
        // TODO: reflect own version
        private val PRODUCER: ByteArray = "emergec".toByteArray(Charsets.UTF_8)
        private val ZERO_WORD = NativeLong(0)
    }
}