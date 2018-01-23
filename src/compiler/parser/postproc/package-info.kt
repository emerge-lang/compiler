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

/**
 * This package contains the code that works unpon the tokens matched by the grammer.
 * It does several things:
 * <ul>
 *      <li>Enhances reportings by recognizing known patterns; adds context info and resolution suggestions</li>
 *      <li>Creates AST data structures from the tokens. These structures have the ability to...<ul>
 *          <li>verify the semantic correctness of the code and provide meaningful error messages if that is not the case</li>
 *          <li>put the code in context with other code in the input (link symbols)</li>
 *          <li>once validated, perform CTFE on the code (if all variables are known at compile time)</li>
 *      </ul></li>
 * </ul>
 */
package compiler.parser.postproc;