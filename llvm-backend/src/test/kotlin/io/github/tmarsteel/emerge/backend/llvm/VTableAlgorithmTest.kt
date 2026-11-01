package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceFile
import io.github.tmarsteel.emerge.backend.api.ir.IrSourceLocation
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmTarget
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.buildVTable
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.missingVirtualFunctionHandler
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants
import io.kotest.core.spec.style.FreeSpec
import io.mockk.every
import io.mockk.mockk
import java.nio.file.Paths
import java.util.stream.Collectors.toMap

/**
 * This class is supposed to prove that the vtable algorithm is suitable for real-world use. C++ doesn't have issues
 * there because every object has one vtable *per* virtual type (which complicates casts extremely). Emerge only has
 * one vtable per concrete type and needs to fit an arbitrary number of virtual types onto the same concrete type.
 */
class VTableAlgorithmTest : FreeSpec({
    val packageName = CanonicalElementName.Package(listOf("vtabletest", randomIdentifier(10)))
    for (nVirtualTypes in 1..10) {
        "for $nVirtualTypes virtual types" - {
            for (nVirtualFunctions in 1..30) {
                "for $nVirtualFunctions virtual functions each" - {
                    val virtualTypes: Set<IrInterface> = (1 .. nVirtualTypes).map { typeN ->
                        val typeName = CanonicalElementName.BaseType(packageName, "V$typeN")
                        lateinit var typeHolder: IrInterface
                        typeHolder = object : IrInterface {
                            override val supertypes = emptySet<IrInterface>()
                            override val canonicalName = typeName
                            override val parameters = emptyList<IrBaseType.Parameter>()
                            override val memberFunctions: List<IrOverloadGroup<IrMemberFunction>> = (1 .. nVirtualFunctions).map { functionN ->
                                SingletonIrOverloadGroup(object : IrMemberFunction {
                                    override val canonicalName = CanonicalElementName.Function(
                                        typeName,
                                        randomIdentifier(4) + "_v" + functionN,
                                    )
                                    override val parameters = listOf(object : IrVariableDeclaration {
                                        override val name = "self"
                                        override val type by lazy { IrSimpleTypeImpl(typeHolder, IrTypeMutability.READONLY, false) }
                                        override val isBorrowed = true
                                        override val isReAssignable = false
                                        override val isSSA = true
                                        override val declaredAt = MockSourceLocation
                                        override val scope = mockk<IrVariableDeclaration.Scope>()
                                    })
                                    override val declaresReceiver = true
                                    override val returnType = IrSimpleTypeImpl(MockIrUnit, IrTypeMutability.READONLY, false)
                                    override val isNothrow = false
                                    override val isExternalC = false
                                    override val body: IrCodeChunk? = null
                                    override val declaredAt = MockSourceLocation
                                    override val ownerBaseType by lazy { typeHolder }
                                    override val overrides = emptySet<IrMemberFunction>()
                                    override val supportsDynamicDispatch = true
                                })
                            }
                        }
                        typeHolder
                    }
                        .toSet()

                    lateinit var concreteType: IrClass
                    concreteType = object : IrClass {
                        override val supertypes: Set<IrInterface> = virtualTypes
                        override val canonicalName = CanonicalElementName.BaseType(
                            packageName,
                            "Concrete"
                        )
                        override val parameters = emptyList<IrBaseType.Parameter>()
                        override val memberFunctions = virtualTypes
                            .flatMap { it.memberFunctions }
                            .flatMap { it.overloads }
                            .map { superFn ->
                                SingletonIrOverloadGroup(object : IrMemberFunction {
                                    override val canonicalName by lazy {
                                        CanonicalElementName.Function(
                                            concreteType.canonicalName,
                                            superFn.canonicalName.simpleName,
                                        )
                                    }
                                    override val parameters = superFn.parameters.mapIndexed { index, parameter ->
                                        if (index > 0) {
                                            return@mapIndexed parameter
                                        }

                                        object : IrVariableDeclaration {
                                            override val name = parameter.name
                                            override val type by lazy { IrSimpleTypeImpl(concreteType, parameter.type.mutability, parameter.type.isNullable) }
                                            override val isBorrowed = parameter.isBorrowed
                                            override val isReAssignable = parameter.isReAssignable
                                            override val isSSA = parameter.isSSA
                                            override val declaredAt = MockSourceLocation
                                            override val scope = mockk<IrVariableDeclaration.Scope>()
                                        }
                                    }
                                    override val declaresReceiver = true
                                    override val returnType = superFn.returnType
                                    override val isNothrow = superFn.isNothrow
                                    override val isExternalC = superFn.isExternalC
                                    override val body: IrCodeChunk = object : IrCodeChunk {
                                        override val components = emptyList<IrExecutable>()
                                    }
                                    override val declaredAt = MockSourceLocation
                                    override val ownerBaseType by lazy { concreteType }
                                    override val overrides = setOf(superFn)
                                    override val supportsDynamicDispatch = true
                                })
                            }
                        override val fields = emptyList<IrClass.Field>()
                        override val constructor = mockk<IrFunction>()
                        override val destructor = mockk<IrFunction>()
                        override val memberVariables = emptyList<IrClass.MemberVariable>()
                        override val declaredAt = MockSourceLocation
                    }

                    val irSoftwareContext = mockk<IrSoftwareContext> {
                        every { modules } returns setOf(mockk {
                            every { packages } returns setOf(
                                mockk {
                                    every { name } returns concreteType.canonicalName.packageName
                                    every { classes } returns setOf(concreteType)
                                    every { interfaces } returns virtualTypes
                                },
                                mockk {
                                    every { name } returns EmergeConstants.CoreModule.NAME
                                    every { classes } returns setOf(object : MockCoreType("Array") {})
                                    every { interfaces } returns emptySet()
                                }
                            )
                        })
                    }

                    EmergeLlvmContext.createDoAndDispose(LlvmTarget.fromTriple("x86_64-pc-linux-gnu"), false) { llvmCtx ->
                        irSoftwareContext.assignVirtualFunctionHashes()
                        llvmCtx.registerBaseType(MockIrUnit)
                        virtualTypes.forEach(llvmCtx::registerBaseType)
                        llvmCtx.registerBaseType(concreteType)
                        // this will throw an exception if a vtable cannot be built
                        buildVTable(
                            llvmCtx,
                            concreteType.memberFunctions
                                .flatMap { it.overloads }
                                .flatMap { fn -> fn.signatureHashes.map { hash -> Pair(hash, fn) }}
                                .onEach { llvmCtx.registerFunction(it.second) }
                                .stream()
                                .collect(toMap(
                                    { it.first },
                                    { it.second.llvmRef!! },
                                )),
                            llvmCtx.registerIntrinsic(missingVirtualFunctionHandler).address,
                        )
                    }
                }
            }
        }
    }
})

private fun randomIdentifier(length: Int): String {
    val chars = (0 .. length).map { ('a' .. 'z').random() }
    return String(chars.toTypedArray().toCharArray())
}
private object MockSourceLocation : IrSourceLocation {
    override val file = object : IrSourceFile {
        override val path = Paths.get("/mock/file.em")
    }
    override val lineNumber: UInt = 1u
    override val columnNumber: UInt = 1u
}
private abstract class MockCoreType(simpleName: String) : IrClass {
    override val supertypes = emptySet<IrInterface>()
    override val canonicalName = CanonicalElementName.BaseType(
        CanonicalElementName.Package(listOf("emerge", "core")),
        simpleName,
    )
    override val parameters = emptyList<IrBaseType.Parameter>()
    override val memberFunctions = emptyList<IrOverloadGroup<IrMemberFunction>>()
    override val memberVariables = emptyList<IrClass.MemberVariable>()
    override val fields = emptyList<IrClass.Field>()
    override val constructor: IrFunction = mockk()
    override val destructor: IrFunction = mockk()
    override val declaredAt = MockSourceLocation
}
private object MockIrUnit : MockCoreType("Unit")
private class SingletonIrOverloadGroup<T : IrFunction>(val single: T) : IrOverloadGroup<T> {
    override val canonicalName by lazy { single.canonicalName }
    override val parameterCount by lazy { single.parameters.size }
    override val overloads = setOf(single)
}