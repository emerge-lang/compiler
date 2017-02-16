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