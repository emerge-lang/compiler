/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

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