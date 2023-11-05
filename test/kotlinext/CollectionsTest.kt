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

package kotlinext

import io.kotest.core.spec.style.StringSpec
import io.kotest.matchers.shouldBe

class CollectionsTest : StringSpec() { init {
    "[1, 2, 3][0..0] == [1]" {
        listOf(1, 2, 3)[0..0] shouldBe listOf(1)
    }

    "[1, 2, 3][2..2] == [3]" {
        listOf(1, 2, 3)[2..2] shouldBe listOf(3)
    }


    "[1, 2, 3][0..1] == [1,2]" {
        listOf(1, 2, 3)[0..1] shouldBe listOf(1, 2)
    }
    "[1, 2, 3][0..2] == [1,2,3]" {
        listOf(1, 2, 3)[0..2] shouldBe listOf(1, 2, 3)
    }
}}