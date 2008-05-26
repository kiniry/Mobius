/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import umbra.editor.parsing.ColorValues;

/**
 * This class is a static container that keeps the value of current colouring
 * style that is obtained after each refreshing (which takes place when
 * a byte code document is created too).
 *
 * This class has two modes of operation:
 * <ul>
 *   <li> The "class unknown" mode - in this case a special greyish colouring
 *        style is returned by the methods. This colouring indicates that the
 *        byte code has no connection with a class file so the editing will not
 *        change any class file.</li>
 *   <li>The "class known" mode - in this case a real colouring style is
 *        returned by the methods. This colouring indicates that the byte code
 *        has connection with a class file so the editing will change the
 *        corresponding class file. This mode is set on in moments when we
 *        know how to associate the class file to its textual representation.
 *        </li>
 * </ul>
 * Most of the time the class of a byte code textual representation that is
 * fed to Umbra is not known so the default mode here is "class unknown" and
 * the intent is to change this mode only for short periods when the class
 * is indeed known.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@smimuw.edu.pl)
 * @version a-01
 */
public final class ColorModeContainer {

  /**
   * The current value of the colouring style. The default colouring style
   * number is 1.
   */
  private static int mod = 1;

  /**
   * The indicator of the normal and special modes. It is equal to
   * <code>false</code> in case the mode is "class unknown" (greyish) and
   * <code>true</code> in case the mode is "class known".
   */
  private static boolean disas; //@ initially false;

  /**
   * The empty constructor to forbid the creation of the instances.
   */
  private ColorModeContainer() {
  }

  /**
   * This method returns the value of the current colouring style mode. In
   * case the current class is in the normal state it returns the greyish
   * style, in case the current class is in the special state it returns
   * the real colouring style.
   *
   * @return the value of the colouring mode to be used
   */
  public static int getMod() {
    if (!disas) return ColorValues.MODES_DESC.length - 1;
    return mod;
  }

  /**
   * This method sets the value of the real colouring style.
   *
   * @param a_color_mode the new value of the real colouring style
   */
  public static void setMod(final int a_color_mode) {
    mod = a_color_mode;
  }

  /**
   * This method sets the mode of the current class to "class known".
   */
  public static void classKnown() {
    disas = true;
  }

  /**
   * This method sets the mode of the current class to "class unknown".
   */
  public static void classUnknown() {
    disas = false;
  }

}
