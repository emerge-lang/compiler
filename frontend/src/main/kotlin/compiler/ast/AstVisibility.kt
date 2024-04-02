package compiler.ast

import compiler.lexer.KeywordToken
import compiler.lexer.Token

sealed class AstVisibility(val nameToken: Token) {
    class Private(keyword: KeywordToken) : AstVisibility(keyword) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Private) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }
    class Module(keyword: KeywordToken) : AstVisibility(keyword) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Module) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }
    class Package(keyword: KeywordToken, val packageName: ASTPackageName) : AstVisibility(keyword) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Package) return false

            if (packageName != other.packageName) return false

            return true
        }

        override fun hashCode(): Int {
            return packageName.hashCode()
        }
    }
    class Export(keyword: KeywordToken) : AstVisibility(keyword) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Export) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }
}