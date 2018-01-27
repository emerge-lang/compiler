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

import com.natpryce.hamkrest.*
import com.natpryce.hamkrest.assertion.assertThat
import compiler.lexer.Keyword.MODULE
import compiler.lexer.Operator.DOT
import compiler.matching.ResultCertainty
import compiler.parser.rule.hasErrors
import matchers.isNotNull
import matchers.isNull

class ModuleDeclarationGrammarTest : GrammarTestCase() { init {
    "singleName" {
        val result = tokenSequence {
            keyword(MODULE)
            identifier("foobar")
            newline()
        }.matchAgainst(ModuleDeclaration)

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)
        val decl = result.item!!
        assertThat(decl.name.size, equalTo(1))
        assertThat(decl.name[0], equalTo("foobar"))
    }

    "twoNames" {
        val result = tokenSequence {
            keyword(MODULE)
            identifier("foo")
            operator(DOT)
            identifier("bar")
            newline()
        }.matchAgainst(ModuleDeclaration)

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)
        val decl = result.item!!
        assertThat(decl.name.size, equalTo(2))
        assertThat(decl.name[0], equalTo("foo"))
        assertThat(decl.name[1], equalTo("bar"))
    }

    "threeNames" {
        val result = tokenSequence {
            keyword(MODULE)
            identifier("foo")
            operator(DOT)
            identifier("bar")
            operator(DOT)
            identifier("baz")
            newline()
        }.matchAgainst(ModuleDeclaration)

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNotNull)
        assertThat(result.reportings, isEmpty)
        val decl = result.item!!
        assertThat(decl.name.size, equalTo(3))
        assertThat(decl.name[0], equalTo("foo"))
        assertThat(decl.name[1], equalTo("bar"))
        assertThat(decl.name[2], equalTo("baz"))
    }

    "missingName" {
        val result = tokenSequence {
            keyword(MODULE)
            newline()
        }.matchAgainst(ModuleDeclaration)

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNull)
        assertThat(result.hasErrors, equalTo(true))
        assertThat(result.reportings, hasSize(equalTo(1)))
        assertThat(result.reportings.first().message, contains(Regex("Unexpected .+?, expecting any identifier")))
    }

    "endsWithDot" {
        val result = tokenSequence {
            keyword(MODULE)
            identifier("foo")
            operator(DOT)
            newline()
        }.matchAgainst(ModuleDeclaration)

        assertThat(result.certainty, greaterThanOrEqualTo(ResultCertainty.MATCHED))
        assertThat(result.item, isNull)
        assertThat(result.hasErrors, equalTo(true))
        assertThat(result.reportings, hasSize(equalTo(1)))

        assertThat(result.reportings.first().message, contains(Regex("Unexpected .+?, expecting any identifier")))
    }
}}