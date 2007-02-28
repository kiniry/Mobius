package b2bpl.translation;

import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JType;


/**
 * Helper class which triggers the translation of different kinds of references
 * encountered during the translation to BoogiePL.
 *
 * <p>
 * This class is thought to be passed to the different classes over which the
 * translation of a Java class to BoogiePL is split. It provides a clean
 * interface to the translation of different kinds of references which may
 * trigger the translation of other parts of the resulting BoogiePL program
 * which are outside the current scope of the translation. Whenever such a
 * context is available, it should always be used to translate the following
 * kinds of references:
 * <ul>
 *   <li>type references</li>
 *   <li>field references</li>
 *   <li>integer literals</li>
 *   <li>string literals</li>
 *   <li>class literals</li>
 * </ul>
 * </p>
 *
 * @author Ovidio Mallo
 */
public interface TranslationContext {

  /**
   * Triggers the translation of the given {@code type} reference and
   * returns a {@code BPLExpression} representing that reference.
   *
   * @param type  The type reference to translate.
   * @return      A {@code BPLExpression} representing the given type
   *              reference.
   */
  BPLExpression translateTypeReference(JType type);

  /**
   * Triggers the translation of the given {@code field} reference and
   * returns a {@code BPLExpression} representing that reference.
   *
   * @param field  The field reference to translate.
   * @return       A {@code BPLExpression} representing the given field
   *               reference.
   */
  BPLExpression translateFieldReference(BCField field);

  /**
   * Triggers the translation of the given integer {@code literal} and
   * returns a {@code BPLExpression} representing that literal.
   *
   * @param literal  The integer literal to translate.
   * @return         A {@code BPLExpression} representing the given integer
   *                 literal.
   */
  BPLExpression translateIntLiteral(long literal);

  /**
   * Triggers the translation of the given string {@code literal} and
   * returns a {@code BPLExpression} representing that literal.
   *
   * @param literal  The string literal to translate.
   * @return         A {@code BPLExpression} representing the given string
   *                 literal.
   */
  BPLExpression translateStringLiteral(String literal);

  /**
   * Triggers the translation of the given class {@code literal} and
   * returns a {@code BPLExpression} representing that literal.
   *
   * @param literal  The class literal to translate.
   * @return         A {@code BPLExpression} representing the given class
   *                 literal.
   */
  BPLExpression translateClassLiteral(JType literal);
}
