package io.github.tmarsteel.emerge.common.config

import com.fasterxml.jackson.core.JsonParseException
import com.fasterxml.jackson.core.JsonParser
import com.fasterxml.jackson.databind.DeserializationContext
import com.fasterxml.jackson.databind.JsonDeserializer
import java.nio.file.Path
import kotlin.io.path.exists
import kotlin.io.path.isDirectory

class DirectoryDeserializer : JsonDeserializer<Path>() {
    override fun deserialize(p: JsonParser, ctxt: DeserializationContext): Path {
        val location = p.currentTokenLocation()
        val asPath = ctxt.readValue(p, Path::class.java)
        if (!asPath.exists() || !asPath.isDirectory()) {
            throw JsonParseException(p, "The path must exist and be a directory", location)
        }

        return asPath
    }
}