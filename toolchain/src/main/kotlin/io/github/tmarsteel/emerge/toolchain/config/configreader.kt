package io.github.tmarsteel.emerge.toolchain.config

import com.fasterxml.jackson.core.JsonParseException
import com.fasterxml.jackson.core.JsonParser
import com.fasterxml.jackson.core.JsonProcessingException
import com.fasterxml.jackson.databind.DeserializationContext
import com.fasterxml.jackson.databind.DeserializationFeature
import com.fasterxml.jackson.databind.JsonDeserializer
import com.fasterxml.jackson.databind.JsonMappingException
import com.fasterxml.jackson.databind.PropertyNamingStrategies
import com.fasterxml.jackson.databind.deser.std.StringDeserializer
import com.fasterxml.jackson.databind.exc.UnrecognizedPropertyException
import com.fasterxml.jackson.databind.module.SimpleModule
import com.fasterxml.jackson.dataformat.yaml.YAMLMapper
import com.fasterxml.jackson.module.kotlin.MissingKotlinParameterException
import com.fasterxml.jackson.module.kotlin.registerKotlinModule
import com.github.ajalt.mordant.rendering.Whitespace
import com.github.ajalt.mordant.terminal.Terminal
import compiler.diagnostic.ReportingException
import compiler.diagnostic.illustrateSourceLocations
import compiler.lexer.DiskLexerSourceFile
import compiler.lexer.MemoryLexerSourceFile
import compiler.lexer.SourceSet
import compiler.lexer.Span
import compiler.lexer.lex
import compiler.parser.grammar.ModuleOrPackageName
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.github.tmarsteel.emerge.common.CanonicalElementName
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.exists
import kotlin.io.path.isRegularFile
import kotlin.io.path.readText
import kotlin.reflect.KClass

private val configObjectMapper = YAMLMapper().also {
    it.registerKotlinModule()
    it.registerModule(ConfigModule)
    it.propertyNamingStrategy = PropertyNamingStrategies.KEBAB_CASE
    it.enable(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES)
}

private object ConfigModule : SimpleModule("EmergeToolchainConfigs") {
    private fun readResolve(): Any = ConfigModule

    val pathsRelativeTo = ScopedValue.newInstance<Path>()

    init {
        addDeserializer(Path::class.java, object : JsonDeserializer<Path>()  {
            override fun deserialize(parser: JsonParser, ctxt: DeserializationContext?): Path? {
                val string = parser.text ?: return null
                val path = Paths.get(string)
                return if (path.isAbsolute) path else pathsRelativeTo.get().resolve(path).normalize()
            }
        })
        addDeserializer(CanonicalElementName.Package::class.java, object : JsonDeserializer<CanonicalElementName.Package>() {
            override fun deserialize(p: JsonParser, ctxt: DeserializationContext): CanonicalElementName.Package {
                val location = p.currentTokenLocation()
                val asString = StringDeserializer.instance.deserialize(p, ctxt)
                val sourceFile = MemoryLexerSourceFile("json input", CanonicalElementName.Package(listOf("cli")), asString)
                val parseResult = matchAgainst(lex(sourceFile), ModuleOrPackageName)
                when (parseResult) {
                    is MatchingResult.Error -> throw JsonParseException(
                        p,
                        parseResult.diagnostic.message,
                        location,
                        ReportingException(parseResult.diagnostic),
                    )
                    is MatchingResult.Success -> return CanonicalElementName.Package(parseResult.item.names.map { it.value })
                }
            }
        })
    }
}

fun <C : Any> Path.parseAsConfig(cclass: KClass<C>): C {
    val selfAbsolute = this.toAbsolutePath()
    require(exists()) { "config file $this not found" }
    require(isRegularFile()) { "$this must be a regular file"}
    return try {
        ScopedValue.callWhere(ConfigModule.pathsRelativeTo, selfAbsolute.parent) {
            configObjectMapper.readValue(selfAbsolute.toFile(), cclass.java)
        }
    } catch (ex: JsonProcessingException) {
        throw ConfigParseException(
            selfAbsolute,
            cclass,
            ex.location.lineNr.toUInt(),
            ex.location.columnNr.toUInt(),
            ex,
        )
    }
}
inline fun <reified C : Any> Path.parseAsConfig(): C = parseAsConfig(C::class)

class ConfigParseException(
    val file: Path,
    val configKClass: KClass<*>,
    val sourceLineNumber: UInt,
    val sourceColumnNumber: UInt,
    override val cause: Throwable,
) : RuntimeException(cause) {
    fun illustrate(to: Terminal) {
        val sourceSet = SourceSet(file.parent, CanonicalElementName.Package(listOf("__config")))
        val sourceFile = DiskLexerSourceFile(sourceSet, file, file.readText())
        val span = Span(sourceFile, sourceLineNumber, sourceColumnNumber, sourceLineNumber, sourceColumnNumber, false)
        val pathRef: List<JsonMappingException.Reference>?
        val message: String
        when (val localCause = cause) {
            is MissingKotlinParameterException -> {
                pathRef = localCause.path.dropLast(1)
                message = "Missing property ${localCause.path.last().fieldName}"
            }
            is UnrecognizedPropertyException -> {
                pathRef = localCause.path
                message = "Unknown property ${localCause.path.last().fieldName}"
            }
            is JsonMappingException -> {
                pathRef = localCause.path
                message = localCause.originalMessage
            }
            else -> {
                message = localCause.message ?: "<no message>"
                pathRef = null
            }
        }
        var fullMessage = "[ERROR] $message\n\n"
        if (pathRef != null) {
            fullMessage += "at ${pathRef.pathReferenceInYAMLNotation}\n"
        }
        fullMessage += "in ${illustrateSourceLocations(listOf(span))}\n"

        to.print(
            message = fullMessage,
            whitespace = Whitespace.PRE,
            stderr = true,
        )
    }
}

private val List<JsonMappingException.Reference>.pathReferenceInYAMLNotation: String get() {
    val sb = StringBuilder()
    var isFirst = true
    for (element in this) {
        if (element.fieldName != null) {
            if (!isFirst) {
                sb.append('.')
            }

            sb.append(element.fieldName)
        } else {
            sb.append('[')
            sb.append(element.index.toString())
            sb.append(']')
        }

        isFirst = false
    }

    return sb.toString()
}