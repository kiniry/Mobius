/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * This object manages the allocation and deallocation of the system
 * colors that are used in the colouring in the bytecode editors.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public final class ColorManager {

  /**
   * The one and only {@link ColorManager} object in the Umbra
   * plugin.
   */
  private static ColorManager manager;

  /**
   * This is a collection that remembers the values of all the already
   * allocated colours. This allows to reuse already allocated colours.
   */
  private Map my_color_table = new HashMap(10);

  /**
   * The private constructor to prevent creating objects otherwise
   * than through the static factory method.
   */
  private ColorManager() {
  }

  /**
   * The static factory which returns the one and only
   * {@link ColorManager} object in the running Umbra plugin.
   *
   * @return the only color manager
   */
  public static ColorManager getColorManager() {
    if (manager == null) {
      manager = new ColorManager();
    }
    return manager;
  }

  /**
   * This method disposes of the operating system resources associated with
   * the colors in the bytecode editor.
   */
  public void dispose() {
    final Iterator e = my_color_table.values().iterator();
    while (e.hasNext())
       ((Color) e.next()).dispose();
  }

  /**
   * This method checks if the menager already has allocated the given
   * value and in that case returns it. In case the value has not been
   * allocated yet, it allocates that from the system display.
   *
   * @param a_rgb the value of the colour to allocate
   * @return the color object for the given RGB value
   */
  public Color getColor(final RGB a_rgb) {
    Color color = (Color) my_color_table.get(a_rgb);
    if (color == null) {
      color = new Color(Display.getCurrent(), a_rgb);
      my_color_table.put(a_rgb, color);
    }
    return color;
  }
}
