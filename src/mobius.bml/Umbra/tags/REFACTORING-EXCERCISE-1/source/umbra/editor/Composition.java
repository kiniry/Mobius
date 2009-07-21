/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

/**
 * This class is a static container that keeps the value of current coloring
 * style that is obtained after each refreshing (which takes place when
 * a bytecode document is created too).
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public final class Composition {

  /**
   * The current value of the colouring style.
   */
  private static int mod = 1;

  /**
   * TODO.
   */
  private static boolean disas; //@ initially false;

  /**
   * TODO.
   */
  private Composition() {
  }

  /**
   * @return if called during disassembling - the current
   * coloring style value;
   * otherwise - it means that bytecode editor is open
   * with no relation to the source, therefore it is colored grey.
   * TODO really?
   */
  public static int getMod() {
    if (!disas) return ColorValues.MODELS.length - 1;
    return mod;
  }

  /**
   * This method sets the current initial colouring style.
   *
   * @param a_color_mode the new value of the initial colouring style
   */
  public static void setMod(final int a_color_mode) {
    mod = a_color_mode;
  }

  /**
   * TODO strange???
   */
  public static void startDisas() {
    disas = true;
  }

  /**
   * TODO.
   */
  public static void stopDisas() {
    disas = false;
  }

}
