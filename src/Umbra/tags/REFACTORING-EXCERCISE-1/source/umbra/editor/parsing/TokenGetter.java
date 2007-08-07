/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.swt.graphics.RGB;

import umbra.editor.ColorManager;
import umbra.editor.ColorValues;
import umbra.editor.NonRuleBasedDamagerRepairer;

/**
 * This method collects array of colors from {@ref ColorValues} class
 * and returns them as a token array.
 * TODO ???
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public final class TokenGetter {

  /**
   * This is a utility class so we declare a private constructor to prevent
   * accidental creation of the instances.
   */
  private TokenGetter() {
  }
  /**
   * @param the_colour_manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param a_mode the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @param a_col a colour value with fixed meaning across the colouring styles
   * @return the colour value as a token
   */
  public static IToken getToken(final ColorManager the_colour_manager,
                                final int a_mode,
                                final int a_col) {
    return new Token(getTextAttribute(the_colour_manager, a_mode, a_col));
  }

  /**
   * @param the_manager the color manager related to the current bytecode
   *    editor, it must be the same as the one in the current
   *    {@ref BytecodeConfiguration} object
   * @param a_mode the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @return Array of tokens for each color value
   *           (for each window element to be coloured)
   *  TODO what the window element is?
   */
  public static IToken[] getTokenTab(final ColorManager the_manager,
                                     final int a_mode) {
    final IToken[] tokens = new IToken[ColorValues.PARTS];
    for (int i = 0; i < ColorValues.PARTS; i++) {
      tokens[i] = TokenGetter.getToken(the_manager, a_mode, i);
    }
    return tokens;
  }

  /**
   * TODO.
   *
   * @param a_manager manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param a_mode the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @param a_col particular color as an attribute
   * @return each time a new damage repairer with the given colour parameters
   */
  public static NonRuleBasedDamagerRepairer getRepairer(
            final ColorManager a_manager,
            final int a_mode,
            final int a_col) {
    return new NonRuleBasedDamagerRepairer(getTextAttribute(a_manager,
                                a_mode, a_col));
  }

  /**
   * TODO.
   *
   * @param the_manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param a_mode the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   * @param a_col a colour value with fixed meaning across the colouring styles
   * @return the given colour as an attribute
   */
  private static TextAttribute getTextAttribute(final ColorManager the_manager,
                          final int a_mode,
                          final int a_col) {
    return new TextAttribute(the_manager.getColor(
             new RGB(ColorValues.MODELS[a_mode][(ColorValues.CN * a_col) +
                                               ColorValues.RED_COMPONENT],
                     ColorValues.MODELS[a_mode][(ColorValues.CN * a_col) +
                                              ColorValues.GREEN_COMPONENT],
                     ColorValues.MODELS[a_mode][(ColorValues.CN * a_col) +
                                              ColorValues.BLUE_COMPONENT])),
                     null,
                     ColorValues.MODELS[a_mode][(ColorValues.CN * a_col) +
                                              ColorValues.STYLE_COMPONENT]);
  }

}
