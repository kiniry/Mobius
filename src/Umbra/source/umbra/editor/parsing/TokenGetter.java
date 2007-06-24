/*
 * Created on 2005-05-13
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.swt.graphics.RGB;

import umbra.editor.ColorManager;
import umbra.editor.IColorValues;
import umbra.editor.NonRuleBasedDamagerRepairer;

/**
 * This method collects array of colors from IColorValues interface
 * and returns them as a token array.
 * TODO ???
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class TokenGetter {

  /**
   * @param manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param mod the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @param i      Position in array of color values
   * @return      Color value as a token
   */
  public static IToken getToken(final ColorManager manager, final int mod, final int i) {
    return new Token(getTextAttribute(manager, mod, i));
  }

  /**
   * @param manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param mod the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @return      Array of tokens for each color value
   *           (for each window element to be coloured)
   */
  public static IToken[] getTokenTab(final ColorManager manager, final int mod) {
    final IToken[] tokens = new IToken[IColorValues.PARTS];
    for (int i = 0; i < IColorValues.PARTS; i++) {
      tokens[i] = TokenGetter.getToken(manager, mod, i);
    }
    return tokens;
  }

  /**
   * TODO
   *
   * @param manager manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param mod the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @param i particular color as an attribute
   */
  public static NonRuleBasedDamagerRepairer getRepairer(
            final ColorManager manager,
            final int mod,
            final int i) {
    return new NonRuleBasedDamagerRepairer(getTextAttribute(manager,
                                mod, i));
  }

  /**
   * TODO
   *
   * @param manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param mod the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @param i      Position in array of color values
   * @return      Particular color as an attribute
   */
  private static TextAttribute getTextAttribute(final ColorManager manager,
                          final int mod,
                          final int i) {
    return new TextAttribute(manager.getColor(
             new RGB(IColorValues.MODELS[mod][(IColorValues.CN * i) +
                                               IColorValues.RED_COMPONENT],
                     IColorValues.MODELS[mod][(IColorValues.CN * i) +
                                              IColorValues.GREEN_COMPONENT],
                     IColorValues.MODELS[mod][(IColorValues.CN * i) +
                                              IColorValues.BLUE_COMPONENT])),
                     null,
                     IColorValues.MODELS[mod][(IColorValues.CN * i) +
                                              IColorValues.STYLE_COMPONENT]);
  }
}
