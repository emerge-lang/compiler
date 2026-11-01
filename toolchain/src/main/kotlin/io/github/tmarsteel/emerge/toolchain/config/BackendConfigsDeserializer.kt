package io.github.tmarsteel.emerge.toolchain.config

import com.fasterxml.jackson.core.JsonParser
import com.fasterxml.jackson.core.JsonToken
import com.fasterxml.jackson.databind.DeserializationContext
import com.fasterxml.jackson.databind.JsonDeserializer
import com.fasterxml.jackson.databind.JsonMappingException
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.toolchain.backends
import kotlin.reflect.KClass

abstract class BackendConfigsDeserializer(
    val getConfigKClass: (EmergeBackend<*, *>) -> KClass<*>
) : JsonDeserializer<Map<EmergeBackend<*, *>, Any>>() {
    override fun deserialize(p: JsonParser, ctx: DeserializationContext): Map<EmergeBackend<*, *>, Any> {
        if (p.currentToken() == JsonToken.START_OBJECT) {
            p.nextToken()
        }

        val result = HashMap<EmergeBackend<*, *>, Any>()
        while (p.currentToken() != JsonToken.END_OBJECT) {
            if (p.currentToken() != JsonToken.FIELD_NAME) {
                ctx.reportWrongTokenException(this, JsonToken.FIELD_NAME, "")
            }
            val backendName = p.text
            val backend = backends[backendName]
                ?: throw JsonMappingException(p, "Unknown backend: $backendName; available: ${backends.keys.joinToString()}")
            p.nextToken()
            val configValue = try {
                ctx.readValue<Any>(p, ctx.constructType(getConfigKClass(backend).java))
            } catch (ex: JsonMappingException) {
                ex.prependPath(result, backendName)
                throw ex
            }
            if (backend in result) {
                throw JsonMappingException(p, "Duplicate entry for key $backendName")
            }
            result[backend] = configValue
            p.nextToken()
        }

        return result
    }
}

class BackendToolchainConfigsDeserializer : BackendConfigsDeserializer(EmergeBackend<*, *>::toolchainConfigKClass)
class BackendProjectConfigsDeserializer : BackendConfigsDeserializer(EmergeBackend<*, *>::projectConfigKClass)