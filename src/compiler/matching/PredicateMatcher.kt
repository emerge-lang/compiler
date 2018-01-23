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

package compiler.matching

open class PredicateMatcher<SubjectType,ErrorType>(
        private val predicate: (SubjectType) -> Boolean,
        override val descriptionOfAMatchingThing: String,
        private val mismatchDescription: (SubjectType) -> ErrorType
) : Matcher<SubjectType, SubjectType, ErrorType>
{
    override fun tryMatch(input: SubjectType): AbstractMatchingResult<SubjectType, ErrorType>
    {
        if (predicate(input))
        {
            return SimpleMatchingResult(ResultCertainty.DEFINITIVE, input)
        }
        else
        {
            return SimpleMatchingResult(ResultCertainty.DEFINITIVE, null, mismatchDescription(input))
        }
    }

    open operator fun invoke(thing: SubjectType): Boolean = predicate(thing)
}