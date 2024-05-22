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
    moduleRef: LlvmModuleRef
) : AutoCloseable {
    private val ref = Llvm.LLVMCreateDIBuilder(moduleRef)
    private val contextRef = Llvm.LLVMGetModuleContext(moduleRef)

    fun createFile(path: Path): DebugInfoScope.File {
        val dirBytes = (path.parent?.toString() ?: "").toByteArray(Charsets.UTF_8)
        val filenameBytes = path.fileName.toString().toByteArray(Charsets.UTF_8)
        val ref = Llvm.LLVMDIBuilderCreateFile(
            ref,
            filenameBytes,
            NativeLong(filenameBytes.size.toLong()),
            dirBytes,
            NativeLong(dirBytes.size.toLong()),
        )

        return DebugInfoScope.File(ref)
    }

    fun createCompileUnit(
        file: DebugInfoScope.File,
        emissionKind: LlvmDwarfEmissionKind = LlvmDwarfEmissionKind.LineTablesOnly,
        forProfiling: Boolean = false,
    ): DebugInfoScope.CompileUnit {
        val ref = Llvm.LLVMDIBuilderCreateCompileUnit(
            ref,
            LlvmDwarfSourceLanguage.C,
            file.ref,
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
        return DebugInfoScope.CompileUnit(ref, file)
    }

    fun createFunction(
        compileUnit: DebugInfoScope.CompileUnit,
        name: CanonicalElementName.Function,
        onLineNumber: UInt
    ): DebugInfoScope.Function {
        val type = NativePointerArray.allocate(0, LlvmMetadataRef::class.java).use { parameterTypesArray ->
            Llvm.LLVMDIBuilderCreateSubroutineType(
                ref,
                compileUnit.file.ref,
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
            compileUnit.file.ref,
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
        scope: LlvmMetadataRef,
        line: UInt,
        column: UInt,
    ): LlvmMetadataRef {
        return Llvm.LLVMDIBuilderCreateDebugLocation(
            contextRef,
            line.toInt(),
            column.toInt(),
            scope,
            null,
        )
    }

    override fun close() {
        Llvm.LLVMDIBuilderFinalize(ref)
        Llvm.LLVMDisposeDIBuilder(ref)
    }

    companion object {
        // TODO: reflect own version
        private val PRODUCER: ByteArray = "emergec".toByteArray(Charsets.UTF_8)
        private val ZERO_WORD = NativeLong(0)
    }
}