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

/**
 * Reported when a value of type [returnedType] is returned from a context where a return type of [expectedReturnType]
 * is expected and the types are not compatible.
 */
class ReturnTypeMismatchReporting(private val base: ValueNotAssignableReporting) : Reporting(
    base.level,
    base.message,
    base.sourceLocation,
) {
    override fun toString(): String = "$levelAndMessage  declared return type is  ${base.targetType}\n  got a value of type      ${base.sourceType}\n\nin $sourceLocation"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ReturnTypeMismatchReporting) return false

        if (base != other.base) return false

        return true
    }

    override fun hashCode(): Int {
        return base.hashCode()
    }
}