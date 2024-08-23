package io.github.tmarsteel.emerge.toolchain

import compiler.InternalCompilerError
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import java.util.ServiceLoader
import java.util.stream.Collectors

internal val backends: Map<String, EmergeBackend<*, *>> = ServiceLoader.load(EmergeBackend::class.java)
    .stream()
    .map { it.get() }
    .collect(Collectors.toMap(
        { it.targetName },
        { it },
        { a, b -> throw InternalCompilerError("Found two backends with name ${a.targetName}: ${a::class.qualifiedName} and ${b::class.qualifiedName}") }
    ))