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

package compiler.reportings

import compiler.lexer.Span

/**
 * An error that results from another one. These should not be shown to an end-user because - assuming the compiler
 * acts as designed - there is another reporting with [Level.ERROR] that describes the root cause.
 * Use this class only if the consecutive error is sever and will likely cause further issues (e.g. because crucial
 * information is missing)
 */
class ConsecutiveFaultDiagnostic(
    message: String,
    span: Span = Span.UNKNOWN
) : Diagnostic(Level.CONSECUTIVE, message, span)