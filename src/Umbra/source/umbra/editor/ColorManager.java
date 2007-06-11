package umbra.editor;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * This object menages the allocation and deallocation of the system
 * colors that are used in the colouring in the bytecode editors.
 *
 * @author Generated automatically
 */

public class ColorManager {

  /**
   * This is a collection that remembers the values of all the already
   * allocated colours. This allows to reuse already allocated colours.
   */
  private Map fColorTable = new HashMap(10);

  /**
   * This method disposes of the operating system resources associated with
   * the colors in the bytecode editor.
   */
  public void dispose() {
    Iterator e = fColorTable.values().iterator();
    while (e.hasNext())
       ((Color) e.next()).dispose();
  }

  /**
   * This method checks if the menager already has allocated the given
   * value and in that case returns it. In case the value has not been
   * allocated yet, it allocates that from the system display.
   *
   * @param rgb the value of the colour to allocate
   * @return the color object for the given RGB value
   */
  public Color getColor(RGB rgb) {
    Color color = (Color) fColorTable.get(rgb);
    if (color == null) {
      color = new Color(Display.getCurrent(), rgb);
      fColorTable.put(rgb, color);
    }
    return color;
  }
}
