/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.swt.graphics.RGB;


/**
 * This is an intermediary class which creates the Eclipse parsing and text
 * partitioning classes with the properties established using the Umbra
 * colouring modes.
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
   * Returns a fresh token with associated colour. The colour is retrieved
   * from the given colour manager and is computed based on the given colouring
   * mode and the colour number within the mode.
   *
   * @param the_colour_manager the colour manager related to the current byte
   *    code editor, it must be the same as in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   * @param a_col a colour value with fixed meaning across the colouring styles
   * @return the colour value as a token
   */
  public static IToken getToken(final ColorManager the_colour_manager,
                                final int a_mode,
                                final int a_col) {
    return new Token(getTextAttribute(the_colour_manager, a_mode, a_col));
  }

  /**
   * Returns the array with tokens for all the possible areas in the BML
   * documents.
   *
   * @param the_manager the colour manager related to the current byte code
   *    editor, it must be the same as the one in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   * @return array of tokens - one for each area
   */
  public static IToken[] getTokenTab(final ColorManager the_manager,
                                     final int a_mode) {
    final IToken[] tokens = new IToken[ColorValues.SLOTS_NO];
    for (int i = 0; i < ColorValues.SLOTS_NO; i++) {
      tokens[i] = TokenGetter.getToken(the_manager, a_mode, i);
    }
    return tokens;
  }

  /**
   * Returns a fresh damager-repairer that determines the damaged region and
   * creates the presentation using the given colour in the given colouring
   * mode with the given colour manager.
   *
   * @param a_manager manager the colour manager related to the current byte
   *    code editor, it must be the same as in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   * @param a_col particular abstract colour as an attribute
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
   * Creates a text attribute for the given colour manager, colouring mode
   * and the colour number. The returned {@link TextAttribute} has the
   * foreground colour set according to the {@link ColorValues#MODES_DESC}
   * array, the background colour set to be the default and the style
   * again set according to the {@link ColorValues#MODES_DESC}.
   *
   * @param the_manager the colour manager related to the current byte code
   *    editor, it must be the same as in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   * @param a_col a colour value with fixed meaning across all the colouring
   *    styles
   * @return the given colour as an attribute
   */
  private static TextAttribute getTextAttribute(final ColorManager the_manager,
                          final int a_mode,
                          final int a_col) {
    return new TextAttribute(the_manager.getColor(
             new RGB(ColorValues.MODES_DESC[a_mode][(
                       ColorValues.COMPONENT_NUMBER * a_col) +
                       ColorValues.COMPONENT_RED],
                     ColorValues.MODES_DESC[a_mode][(
                       ColorValues.COMPONENT_NUMBER * a_col) +
                       ColorValues.COMPONENT_GREEN],
                     ColorValues.MODES_DESC[a_mode][(
                       ColorValues.COMPONENT_NUMBER * a_col) +
                       ColorValues.COMPONENT_BLUE])),
                     null,
                     ColorValues.MODES_DESC[a_mode][(
                       ColorValues.COMPONENT_NUMBER * a_col) +
                       ColorValues.COMPONENT_TXTSTYLE]);
  }

}
