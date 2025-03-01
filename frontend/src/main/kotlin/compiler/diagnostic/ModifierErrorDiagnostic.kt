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

package compiler.diagnostic

import compiler.lexer.Span

/**
 * Reported on generic modifier *errors*, e.g. when
 * * incompatible modifiers are present (declared or implicit) on the same element, e.g. the type `mutable Int`:
 *   explicit `mutable` is not compatible with implicit `immutable`
 */
class ModifierErrorDiagnostic(
    message: String,
    location: Span
) : Diagnostic(Severity.ERROR, message, location)