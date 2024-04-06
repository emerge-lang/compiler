package compiler.ast

import compiler.binding.BoundVisibility
import compiler.binding.context.CTContext
import compiler.lexer.KeywordToken
import compiler.lexer.Token

sealed class AstVisibility(nameToken: Token) : AstFunctionAttribute(nameToken) {
    abstract fun bindTo(context: CTContext) : BoundVisibility

    class Private(keyword: KeywordToken) : AstVisibility(keyword) {
        override fun bindTo(context: CTContext): BoundVisibility {
            return BoundVisibility.FileScope(context, this)
        }

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
        override fun bindTo(context: CTContext): BoundVisibility {
            return BoundVisibility.PackageScope(context, context.moduleContext.moduleName, this, false)
        }

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
        override fun bindTo(context: CTContext): BoundVisibility {
            return BoundVisibility.PackageScope(context, packageName.asDotName, this, false)
        }

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
        override fun bindTo(context: CTContext): BoundVisibility {
            return BoundVisibility.ExportedScope(context, this)
        }

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