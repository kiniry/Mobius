package mobius.prover.gui.editor;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * An interface to define some basic colors and tags to use with
 * the rules and/or scanners.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IColorConstants {
  /** Text is black. */
  Color DEFAULT_TAG_COLOR = new Color(Display.getCurrent(), new RGB(0, 0, 0));

  // Some background colors
  /** the hilight color: grey 200, 200, 200.*/
  Color HILIT_COLOR = 
    new Color(Display.getCurrent(), new RGB(200, 200, 200));
  
  /** the background color: white 255, 255, 255.*/
  Color NORMAL_COLOR = 
    new Color(Display.getCurrent(), new RGB(255, 255, 255));
  
  // Some colors...
  /** the color white 255, 255, 255.*/
  Color WHITE = new Color(Display.getCurrent(), new RGB(255, 255, 255));
  /** the color red 255, 0, 0.*/
  Color RED = new Color(Display.getCurrent(), new RGB(255, 0, 0));
  /** the color darkred 155, 0, 0.*/
  Color DARKRED = new Color(Display.getCurrent(), new RGB(155, 0, 0));
  /** the color green 0, 155, 0.*/
  Color GREEN = new Color(Display.getCurrent(), new RGB(0, 155, 0));
  /** the color blue 0, 0, 220.*/
  Color BLUE = new Color(Display.getCurrent(), new RGB(0, 0, 220));
  /** the color grey 100, 100, 100.*/
  Color GREY = new Color(Display.getCurrent(), new RGB(100, 100, 100));
  /** the color violet 100, 0, 100.*/
  Color VIOLET = new Color(Display.getCurrent(), new RGB(100, 0, 100));

}
