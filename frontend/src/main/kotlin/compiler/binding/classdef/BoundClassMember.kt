package compiler.binding.classdef

import compiler.binding.SemanticallyAnalyzable

sealed interface BoundClassMember : BoundClassEntry, SemanticallyAnalyzable {
    val name: String
}