package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import java.math.BigInteger
import java.nio.file.Path
import java.nio.file.Paths
import java.security.MessageDigest
import kotlin.io.path.createDirectories
import kotlin.io.path.exists
import kotlin.io.path.writeBytes

fun <T> Iterable<T>.indexed(): Iterable<Pair<Int, T>> = object : Iterable<Pair<Int, T>> {
    override fun iterator(): Iterator<Pair<Int, T>> = object : Iterator<Pair<Int, T>> {
        val inner = this@indexed.iterator()
        var index = 0

        override fun hasNext() = inner.hasNext()

        override fun next(): Pair<Int, T> {
            val element = Pair(index, inner.next())
            index += 1
            return element
        }
    }
}

val RESOURCE_CACHE_DIR: Path get() = System.getProperty("emerge.backend.llvm.cache-dir", null)
    ?.let(Paths::get)
    ?: Paths.get(System.getProperty("user.dir")).resolve(".emerge-compiler-cache").resolve("llvm-backend")

fun getClasspathResourceAsFileOnDisk(
    clazz: Class<*>,
    resource: String,
    cacheDir: Path = RESOURCE_CACHE_DIR,
): Path {
    val resourceUrl = clazz.getResource(resource)
        ?: throw CodeGenerationException("Classpath resource $resource not found in classloader ${clazz.classLoader.name}")

    if (resourceUrl.protocol == "file") {
        if (System.getProperty("file.separator") == "/") {
            // on linux: the URL will be file:/root/subdir, and the path field is the /root/subdir part, which is correct
            return Paths.get(resourceUrl.path)
        } else {
            // on windows: the path will be /C:/root/subdir, which won't work
            return Paths.get(resourceUrl.path.removePrefix("/"))
        }
    }

    cacheDir.createDirectories()
    val payload = resourceUrl.readBytes()
    val hash = run {
        val md = MessageDigest.getInstance("MD5")
        md.update(payload)
        BigInteger(1, md.digest()).toString(36).lowercase()
    }
    val path = cacheDir.resolve(Paths.get(resourceUrl.file).fileName.toString() + ".$hash")
    if (!path.exists()) {
        path.writeBytes(payload)
    }
    return path
}