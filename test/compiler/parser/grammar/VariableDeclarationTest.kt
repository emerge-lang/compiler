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

import compiler.ast.expression.Expression
import compiler.ast.type.TypeReference
import compiler.lexer.Keyword.VAL
import compiler.lexer.Keyword.VAR
import compiler.lexer.Operator.ASSIGNMENT
import compiler.lexer.Operator.COLON
import compiler.matching.ResultCertainty.DEFINITIVE
import io.kotlintest.matchers.shouldBe
import io.kotlintest.matchers.shouldEqual
import io.kotlintest.matchers.shouldNotBe
import io.kotlintest.mock.mock
import java.util.*

class VariableDeclarationTest : GrammarTestCase() {init {
    "most simple" {
        val result = tokenSequence {
            keyword(VAR)
            identifier("someVar")
            newline()
        }.matchAgainst(VariableDeclaration)

        result.certainty shouldBe DEFINITIVE
        result.item shouldNotBe null
        val ast = result.item!!
        ast.initializerExpression shouldBe null
        ast.name.value shouldEqual "someVar"
        ast.typeModifier shouldBe null
        ast.type shouldBe null
        ast.isAssignable shouldBe true
    }

    "all features" - {
        val mockTypeReference = mock<TypeReference>()
        val mockInitializer = mock<Expression<*>>()
        val mockTypeModifier = compiler.ast.type.TypeModifier.values()[Random().nextInt(compiler.ast.type.TypeModifier.values().size)]

        val result = tokenSequence {
            mockRef(mockTypeModifier)
            keyword(VAR)
            identifier("someVarTwo")
            operator(COLON)
            mockRef(mockTypeReference)
            operator(ASSIGNMENT)
            mockRef(mockInitializer)
            newline()
        }.matchAgainst(VariableDeclaration)

        result.certainty shouldBe DEFINITIVE
        result.item shouldNotBe null

        val ast = result.item!!

        "type modifier is recognized" {
            ast.typeModifier shouldBe mockTypeModifier
        }

        "name is recognized" {
            ast.name.value shouldEqual "someVarTwo"
        }

        "type is recognized" {
            ast.type shouldBe mockTypeReference
        }

        "initializer expression is recognized" {
            ast.initializerExpression shouldBe mockInitializer
        }
    }

    "assignability" - {
        "var is assignable" {
            val result = tokenSequence {
                keyword(VAR)
                identifier("someVar")
                newline()
            }.matchAgainst(VariableDeclaration)

            result.certainty shouldBe DEFINITIVE
            result.item shouldNotBe null

            val ast = result.item!!

            ast.isAssignable shouldBe true
        }

        "val is not assignable" {
            val result = tokenSequence {
                keyword(VAL)
                identifier("someVar")
                newline()
            }.matchAgainst(VariableDeclaration)

            result.certainty shouldBe DEFINITIVE
            result.item shouldNotBe null

            val ast = result.item!!

            ast.isAssignable shouldBe false
        }
    }
}}