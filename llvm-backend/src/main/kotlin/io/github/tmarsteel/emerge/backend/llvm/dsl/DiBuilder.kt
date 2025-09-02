package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.sun.jna.NativeLong
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.backend.llvm.jna.DwarfBaseTypeEncoding
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmBasicBlockRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDiFlags
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfEmissionKind
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmDwarfSourceLanguage
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmModuleRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativeI32FlagGroup
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.nio.file.Path

class DiBuilder(
    val context: LlvmContext,
    moduleRef: LlvmModuleRef,
    filePath: Path,
    emissionKind: LlvmDwarfEmissionKind = LlvmDwarfEmissionKind.Full,
    forProfiling: Boolean = false,
) : AutoCloseable {
    private val ref = Llvm.LLVMCreateDIBuilder(moduleRef)

    val file: LlvmDebugInfo.Scope.File
    val compileUnit: LlvmDebugInfo.Scope.CompileUnit

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
        file = LlvmDebugInfo.Scope.File(fileRef, filePath)

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
        compileUnit = LlvmDebugInfo.Scope.CompileUnit(compileUnitRef, filePath.toString())
    }

    private val structTypeTags = HashMap<String, UInt>()
    fun getStructTypeTag(uniqueId: String): UInt {
        val next = (structTypeTags.size + 1).toUInt()
        return structTypeTags.putIfAbsent(uniqueId, next) ?: next
    }

    fun createSubroutineParameter(
        scope: LlvmDebugInfo.Scope.Function,
        name: String,
        index: UInt,
        lineNumber: UInt,
        type: LlvmDebugInfo.Type,
        alwaysPreserve: Boolean = false,
        flags: NativeI32FlagGroup<LlvmDiFlags> = NativeI32FlagGroup(),
    ): LlvmDebugInfo.LocalVariable {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        val ref = Llvm.LLVMDIBuilderCreateParameterVariable(
            ref,
            scope.ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            (index + 1u).toInt(),
            file.ref,
            lineNumber.toInt(),
            type.ref,
            if (alwaysPreserve) 1 else 0,
            flags,
        )
        return LlvmDebugInfo.LocalVariable(ref)
    }

    fun createSubroutineType(
        parameterTypes: Collection<LlvmDebugInfo.Type>,
    ): LlvmDebugInfo.SubroutineType {
        check(!closed)

        NativePointerArray.fromJavaPointers(parameterTypes.map { it.ref }).use { parameterTypesArray ->
            return LlvmDebugInfo.SubroutineType(Llvm.LLVMDIBuilderCreateSubroutineType(
                ref,
                file.ref,
                parameterTypesArray,
                parameterTypesArray.length,
                0,
            ))
        }
    }

    fun createFunction(
        name: String,
        linkageName: String = name,
        onLineNumber: UInt,
        subroutineType: LlvmDebugInfo.SubroutineType,
    ): LlvmDebugInfo.Scope.Function {
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
            subroutineType.ref,
            1, // TODO: defer from visibility
            1,
            0,
            0,
            0,
        )

        return LlvmDebugInfo.Scope.Function(ref, name.toString())
    }

    fun createDebugLocation(
        scope: LlvmDebugInfo.Scope,
        line: UInt,
        column: UInt,
    ): LlvmDebugInfo.Location {
        check(!closed)

        return LlvmDebugInfo.Location(Llvm.LLVMDIBuilderCreateDebugLocation(
            context.ref,
            line.toInt(),
            column.toInt(),
            scope.ref,
            null,
        ))
    }

    fun createLexicalScope(
        parentScope: LlvmDebugInfo.Scope?,
        line: UInt,
        column: UInt,
    ): LlvmDebugInfo.Scope.LexicalBlock {
        check(!closed)

        val blockRef = Llvm.LLVMDIBuilderCreateLexicalBlock(
            ref,
            parentScope?.ref ?: file.ref,
            file.ref,
            line.toInt(),
            column.toInt(),
        )

        return LlvmDebugInfo.Scope.LexicalBlock(blockRef)
    }

    fun createBasicType(
        name: String,
        sizeInBits: ULong,
        encoding: DwarfBaseTypeEncoding,
    ): LlvmDebugInfo.Type {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        return LlvmDebugInfo.Type(Llvm.LLVMDIBuilderCreateBasicType(
            ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong()),
            sizeInBits.toLong(),
            encoding,
            NativeI32FlagGroup(),
        ));
    }

    fun createUnspecifiedType(name: String): LlvmDebugInfo.Type {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        return LlvmDebugInfo.Type(Llvm.LLVMDIBuilderCreateUnspecifiedType(
            ref,
            nameBytes,
            NativeLong(nameBytes.size.toLong())
        ))
    }

    fun createStructMember(
        name: String,
        sizeInBits: ULong,
        alignInBits: UInt,
        offsetInBits: ULong,
        type: LlvmDebugInfo.Type,
        flags: NativeI32FlagGroup<LlvmDiFlags>,
        declaredAt: IrSourceLocation,
    ): LlvmDebugInfo.StructMember {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)

        return LlvmDebugInfo.StructMember(Llvm.LLVMDIBuilderCreateMemberType(
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
            type.ref,
        ))
    }

    fun createStructType(
        name: String,
        sizeInBits: ULong,
        alignInBits: UInt,
        flags: NativeI32FlagGroup<LlvmDiFlags>,
        elements: List<LlvmDebugInfo.StructMember>?,
        declaredAt: IrSourceLocation?,
    ): LlvmDebugInfo.Type {
        check(!closed)

        val nameBytes = name.toByteArray(Charsets.UTF_8)
        val nameBytesLen = NativeLong(nameBytes.size.toLong())

        return NativePointerArray.fromJavaPointers(elements?.map { it.ref } ?: emptyList()).use { elementsArray ->
            LlvmDebugInfo.Type(Llvm.LLVMDIBuilderCreateStructType(
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
            ))
        }
    }

    fun createTemporaryForwardDeclarationOfStructType(
        name: String,
        uniqueId: String = name,
        sizeInBits: ULong,
        alignInBits: UInt,
        flags: NativeI32FlagGroup<LlvmDiFlags>,
        declaredAt: IrSourceLocation,
    ): LlvmDebugInfo.Type {
        val nameBytes = name.toByteArray(Charsets.UTF_8)
        val nameBytesLen = NativeLong(nameBytes.size.toLong())
        val uniqueIdBytes: ByteArray
        val uniqueIdLen: NativeLong
        if (uniqueId == name) {
            uniqueIdBytes = nameBytes
            uniqueIdLen = nameBytesLen
        } else {
            uniqueIdBytes = uniqueId.toByteArray(Charsets.UTF_8)
            uniqueIdLen = NativeLong(uniqueIdBytes.size.toLong())
        }

        return LlvmDebugInfo.Type(Llvm.LLVMDIBuilderCreateReplaceableCompositeType(
            ref,
            getStructTypeTag(uniqueId).toInt(),
            nameBytes,
            nameBytesLen,
            file.ref,
            file.ref,
            declaredAt.lineNumber.toInt(),
            0,
            sizeInBits.toLong(),
            alignInBits.toInt(),
            flags,
            uniqueIdBytes,
            uniqueIdLen,
        ))
    }

    fun createPointerType(
        pointeeType: LlvmDebugInfo.Type,
    ): LlvmDebugInfo.Type {
        check(!closed)

        return LlvmDebugInfo.Type(Llvm.LLVMDIBuilderCreatePointerType(
            ref,
            pointeeType.ref,
            context.targetData.pointerSizeInBits.toLong(),
            0,
            0,
            null,
            null,
        ))
    }

    fun createArrayType(
        elementType: LlvmDebugInfo.Type,
        size: ULong,
        alignInBits: UInt
    ): LlvmDebugInfo.Type {
        check(!closed)

        return LlvmDebugInfo.Type(Llvm.LLVMDIBuilderCreateArrayType(
            ref,
            size.toLong(),
            alignInBits.toInt(),
            elementType.ref,
            null,
            0,
        ))
    }

    fun createExpression(): LlvmDebugInfo.Expression {
        return LlvmDebugInfo.Expression(
            Llvm.LLVMDIBuilderCreateExpression(ref, null, NativeLong(0))
        )
    }

    fun createConstantValueExpression(value: ULong): LlvmDebugInfo.Expression {
        return LlvmDebugInfo.Expression(
            Llvm.LLVMDIBuilderCreateConstantValueExpression(ref, value.toLong())
        )
    }

    fun insertDeclareRecordAtEndOfBasicBlock(
        storage: LlvmValue<*>,
        varInfo: LlvmDebugInfo.LocalVariable,
        expression: LlvmDebugInfo.Expression,
        declaredAt: LlvmDebugInfo.Location,
        block: LlvmBasicBlockRef,
    ) {
        check(!closed)

        Llvm.LLVMDIBuilderInsertDeclareRecordAtEnd(
            ref,
            storage.raw,
            varInfo.ref,
            expression.ref,
            declaredAt.ref,
            block,
        )
    }

    fun insertValueRecordAtEndOfBasicBlock(
        storage: LlvmValue<*>,
        varInfo: LlvmDebugInfo.LocalVariable,
        expression: LlvmDebugInfo.Expression,
        declaredAt: LlvmDebugInfo.Location,
        block: LlvmBasicBlockRef,
    ) {
        check(!closed)

        Llvm.LLVMDIBuilderInsertDbgValueRecordAtEnd(
            ref,
            storage.raw,
            varInfo.ref,
            expression.ref,
            declaredAt.ref,
            block,
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