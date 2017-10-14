package compiler.parser.grammar

import ModuleDeclaration
import compiler.matching.ResultCertainty
import io.kotlintest.matchers.shouldEqual

class ModuleDeclarationTest : GrammarTestCase() { init {
    "singleName" {
        val tokens = lex("module foobar\n")
        val result = ModuleDeclaration.tryMatch(tokens)

        assert(result.certainty >= ResultCertainty.MATCHED)
        assert(result.item != null)
        assert(result.reportings.isEmpty())
        val decl = result.item!!
        decl.name.size shouldEqual 1
        decl.name[0] shouldEqual "foobar"
    }

    "twoNames" {
        val tokens = lex("module foo.bar\n")
        val result = ModuleDeclaration.tryMatch(tokens)

        assert(result.certainty >= ResultCertainty.MATCHED)
        assert(result.item != null)
        assert(result.reportings.isEmpty())
        val decl = result.item!!
        decl.name.size shouldEqual 2
        decl.name[0] shouldEqual "foo"
        decl.name[1] shouldEqual "bar"
    }

    "threeNames" {
        val tokens = lex("module foo.bar.baz\n")
        val result = ModuleDeclaration.tryMatch(tokens)

        assert(result.certainty >= ResultCertainty.MATCHED)
        assert(result.item != null)
        assert(result.reportings.isEmpty())
        val decl = result.item!!
        decl.name.size shouldEqual 3
        decl.name[0] shouldEqual "foo"
        decl.name[1] shouldEqual "bar"
        decl.name[2] shouldEqual "baz"
    }

    // TODO: error cases
}}