package compiler.parser.grammar

import com.natpryce.hamkrest.assertion.assertThat
import com.natpryce.hamkrest.equalTo
import com.natpryce.hamkrest.greaterThanOrEqualTo
import com.natpryce.hamkrest.isEmpty
import compiler.matching.ResultCertainty
import matchers.isNotNull
import matchers.isNull

class TypesGrammarTest : GrammarTestCase() {init {
    "simple" {
        val result = Type.tryMatch(lex("Typename"))

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)

        val typeRef = result.item!!
        assertThat(typeRef.declaredName, equalTo("Typename"))
        assertThat(typeRef.isNullable, equalTo(false))
        assertThat(typeRef.modifier, isNull)
    }

    "nullable" {
        val result = Type.tryMatch(lex("Typename?"))

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)

        val typeRef = result.item!!
        assertThat(typeRef.declaredName, equalTo("Typename"))
        assertThat(typeRef.isNullable, equalTo(true))
        assertThat(typeRef.modifier, isNull)
    }

    "modified" {
        val result = Type.tryMatch(lex("immutable Typename"))

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)

        val typeRef = result.item!!
        assertThat(typeRef.declaredName, equalTo("Typename"))
        assertThat(typeRef.isNullable, equalTo(false))
        assertThat(typeRef.modifier, equalTo(compiler.ast.type.TypeModifier.IMMUTABLE))
    }

    "modified nullable" {
        val result = Type.tryMatch(lex("mutable Typename?"))

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)

        val typeRef = result.item!!
        assertThat(typeRef.declaredName, equalTo("Typename"))
        assertThat(typeRef.isNullable, equalTo(true))
        assertThat(typeRef.modifier, equalTo(compiler.ast.type.TypeModifier.MUTABLE))
    }
}}