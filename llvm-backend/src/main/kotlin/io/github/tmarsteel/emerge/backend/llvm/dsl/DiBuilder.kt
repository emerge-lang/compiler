package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.backend.llvm.jna.DwarfBaseTypeEncoding
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDiFlags
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfEmissionKind
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfSourceLanguage
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmModuleRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativeI32FlagGroup
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import io.github.tmarsteel.emerge.common.CanonicalElementName
import java.nio.file.Path

class DiBuilder(
    val context: LlvmContext,
    moduleRef: LlvmModuleRef,
    filePath: Path,
    emissionKind: LlvmDwarfEmissionKind = LlvmDwarfEmissionKind.Full,
    forProfiling: Boolean = false,
) : AutoCloseable {
    private val ref = Llvm.LLVMCreateDIBuilder(moduleRef)

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
        file = DebugInfoScope.File(fileRef, filePath)

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
        compileUnit = DebugInfoScope.CompileUnit(compileUnitRef, filePath.toString())
    }

    private val structTypeTags = HashMap<CanonicalElementName.BaseType, UInt>()
    fun getStructTypeTag(name: CanonicalElementName.BaseType): UInt {
        val next = (structTypeTags.size + 1).toUInt()
        return structTypeTags.putIfAbsent(name, next) ?: next
    }

    fun createSubroutineParameter(
        name: String,
        index: UInt,
        lineNumber: UInt,
        type: LlvmMetadataRef,
        alwaysPreserve: Boolean = false,
        flags: NativeI32FlagGroup<LlvmDiFlags> = NativeI32FlagGroup(),
    ): LlvmMetadataRef {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        return Llvm.LLVMDIBuilderCreateParameterVariable(
            ref,
            file.ref, // TODO: this doesn't work, needs to be a DILocalScope
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            (index + 1u).toInt(),
            file.ref,
            lineNumber.toInt(),
            type,
            if (alwaysPreserve) 1 else 0,
            flags,
        )
    }

    fun createSubroutineType(
        parameters: Collection<LlvmMetadataRef>,
    ): LlvmMetadataRef {
        check(!closed)

        NativePointerArray.fromJavaPointers(parameters).use { parametersArray ->
            return Llvm.LLVMDIBuilderCreateSubroutineType(
                ref,
                file.ref,
                parametersArray,
                parametersArray.length,
                0,
            )
        }
    }

    fun createFunction(
        name: String,
        linkageName: String = name,
        onLineNumber: UInt,
        subroutineType: LlvmMetadataRef,
    ): DebugInfoScope.Function {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)
        val linkageNameBytes = if (linkageName == name) nameBytes else linkageName.toByteArray(Charsets.UTF_8)

        val ref = Llvm.LLVMDIBuilderCreateFunction(
            ref,
            file.ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            linkageNameBytes,
            NativeLong(linkageNameBytes.size.toLong()),
            file.ref,
            onLineNumber.toInt(),
            subroutineType,
            1, // TODO: defer from visibility
            1,
            0,
            0,
            0,
        )

        return DebugInfoScope.Function(ref, name.toString())
    }

    fun createDebugLocation(
        scope: DebugInfoScope,
        line: UInt,
        column: UInt,
    ): LlvmMetadataRef {
        check(!closed)

        return Llvm.LLVMDIBuilderCreateDebugLocation(
            context.ref,
            line.toInt(),
            column.toInt(),
            scope.ref,
            null,
        )
    }

    fun createBasicType(
        name: String,
        sizeInBits: ULong,
        encoding: DwarfBaseTypeEncoding,
    ): LlvmMetadataRef {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        return Llvm.LLVMDIBuilderCreateBasicType(
            ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            sizeInBits.toLong(),
            encoding,
            NativeI32FlagGroup(),
        );
    }

    fun createStructMember(
        name: String,
        sizeInBits: ULong,
        alignInBits: UInt,
        offsetInBits: ULong,
        type: LlvmMetadataRef,
        flags: NativeI32FlagGroup<LlvmDiFlags>,
        declaredAt: IrSourceLocation,
    ): LlvmMetadataRef {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        return Llvm.LLVMDIBuilderCreateMemberType(
            ref,
            file.ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            file.ref,
            declaredAt.lineNumber.toInt(),
            sizeInBits.toLong(),
            alignInBits.toLong(),
            offsetInBits.toLong(),
            flags,
            type,
        )
    }

    fun createStructType(
        name: String,
        sizeInBits: ULong,
        alignInBits: UInt,
        flags: NativeI32FlagGroup<LlvmDiFlags>,
        elements: List<LlvmMetadataRef>,
        declaredAt: IrSourceLocation?,
    ): LlvmMetadataRef {
        check(!closed)

        val nameBytes = name.toString().toByteArray(Charsets.UTF_8)
        val nameBytesLen = NativeLong(nameBytes.size.toLong())

        return NativePointerArray.fromJavaPointers(elements).use { elementsArray ->
            Llvm.LLVMDIBuilderCreateStructType(
                ref,
                file.ref,
                nameBytes,
                nameBytesLen,
                file.ref,
                declaredAt?.lineNumber?.toInt() ?: 0,
                sizeInBits.toLong(),
                alignInBits.toInt(),
                flags,
                null,
                elementsArray,
                elementsArray.length,
                0,
                null,
                nameBytes,
                nameBytesLen,
            )
        }
    }

    fun createForwardDeclarationOfStructType(
        name: CanonicalElementName.BaseType,
        sizeInBits: ULong,
        alignInBits: UInt,
        flags: NativeI32FlagGroup<LlvmDiFlags>,
        declaredAt: IrSourceLocation,
    ): LlvmMetadataRef {
        val nameBytes = name.toString().toByteArray(Charsets.UTF_8)
        val nameBytesLen = NativeLong(nameBytes.size.toLong())

        return Llvm.LLVMDIBuilderCreateReplaceableCompositeType(
            ref,
            getStructTypeTag(name).toInt(),
            nameBytes,
            nameBytesLen,
            file.ref,
            file.ref,
            declaredAt.lineNumber.toInt(),
            0,
            sizeInBits.toLong(),
            alignInBits.toInt(),
            flags,
            nameBytes,
            nameBytesLen,
        )
    }

    fun createPointerType(
        pointeeType: LlvmMetadataRef,
    ): LlvmMetadataRef {
        check(!closed)

        return Llvm.LLVMDIBuilderCreatePointerType(
            ref,
            pointeeType,
            context.targetData.pointerSizeInBits.toLong(),
            0,
            0,
            null,
            null,
        )
    }

    fun createArrayType(
        elementType: LlvmMetadataRef,
        size: ULong,
        alignInBits: UInt
    ): LlvmMetadataRef {
        check(!closed)

        return Llvm.LLVMDIBuilderCreateArrayType(
            ref,
            size.toLong(),
            alignInBits.toInt(),
            elementType,
            null,
            0,
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