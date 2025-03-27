package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.llvm.intrinsics.PointerToEmergeArrayOfPointersToTypeInfoType
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.kotest.common.ExperimentalKotest
import io.kotest.core.config.AbstractProjectConfig
import io.kotest.core.spec.IsolationMode
import java.nio.file.Paths

object KotestProjectConfig : AbstractProjectConfig() {
    @Volatile
    private var loaded = false
    private val loadingMutex = Any()

    override suspend fun beforeProject() {
        assureLlvmIsDynamicallyLinked()
    }

    override val parallelism: Int = Runtime.getRuntime().availableProcessors()

    private fun assureLlvmIsDynamicallyLinked() {
        if (loaded) {
            return
        }
        synchronized(loadingMutex) {
            if (loaded) {
                return
            }

            val propertyName = "emerge.llvm-tests.llvm-install-dir"
            val installDirString = System.getProperty(propertyName)
                ?: error("Missing system property $propertyName")
            val installDir = Paths.get(installDirString)
            loaded = true
            Llvm.loadNativeLibrary(installDir)
            Llvm.LLVMInitializeX86TargetInfo()
            Llvm.LLVMInitializeX86Target()
            Llvm.LLVMInitializeX86TargetMC()
            Llvm.LLVMInitializeX86AsmPrinter()
            Llvm.LLVMInitializeX86AsmParser()
        }
    }
}