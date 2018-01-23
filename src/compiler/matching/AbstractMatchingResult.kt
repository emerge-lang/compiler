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


/**
 * When a [Matcher] is matched against an input it returns an [AbstractMatchingResult] that describes
 * the outcome of the matching process.
 *
 * If there was no doubt about the input is of the structure the matcher expects the [certainty] must be
 * [ResultCertainty.DEFINITIVE]; if the given input is ambigous (e.g. does not have properties unique to the
 * [Matcher]), the [certainty] should be [ResultCertainty.NOT_RECOGNIZED].
 *
 * Along with the [item] of the match, an [AbstractMatchingResult] can provide the caller with additional reportings
 * about the matched input. If the input did not match the expectations of the [Matcher] that could be details on what
 * expectations were not met.
 *
 * The [item] may only be null if the given input did not contain enough information to construct a meaningful item.
 */
interface AbstractMatchingResult<out ItemType,ReportingType> {
    val certainty: ResultCertainty
    val item: ItemType?
    val reportings: Collection<ReportingType>

    companion object {
        fun <ItemType, ReportingType> ofResult(result: ItemType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ItemType, ReportingType> {
            return object : AbstractMatchingResult<ItemType, ReportingType> {
                override val certainty = certainty
                override val item = result
                override val reportings = emptySet<ReportingType>()
            }
        }

        fun <ItemType, ReportingType> ofError(error: ReportingType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ItemType, ReportingType> {
            return object : AbstractMatchingResult<ItemType, ReportingType> {
                override val certainty = certainty
                override val item = null
                override val reportings = setOf(error)
            }
        }

        inline fun <T, reified ItemType, reified ReportingType> of(thing: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ItemType, ReportingType> {
            if (thing is ItemType) return ofResult(thing, certainty)
            if (thing is ReportingType) return ofError(thing, certainty)
            throw IllegalArgumentException("Given object is neither of item type nor of error type")
        }
    }
}