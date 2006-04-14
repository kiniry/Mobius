package prover.gui.editor;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * An interface to define some basic colors and tags to use with
 * the rules and/or scanners.
 * @author J. Charles
 *
 */
public interface IColorConstants {
	// Text is black
	public final static Color DEFAULT_TAG_COLOR = new Color(Display.getCurrent(), 
			new RGB(0,0,0));

	// Some background colors
	public final static Color HILIT_COLOR = 
		new Color(Display.getCurrent(), new RGB(200, 200, 200));
	public final static Color NORMAL_COLOR = 
		new Color(Display.getCurrent(), new RGB(255, 255, 255));
	
	// Some colors...
	public final static Color WHITE = new Color(Display.getCurrent(), new RGB(255, 255, 255));
	public final static Color RED = new Color(Display.getCurrent(), new RGB(255, 0, 0));
	public final static Color DARKRED = new Color(Display.getCurrent(), new RGB(155, 0, 0));
	public final static Color GREEN = new Color(Display.getCurrent(), new RGB(0, 155, 0));
	public final static Color BLUE= new Color(Display.getCurrent(), new RGB(0, 0, 220));
	public final static Color GREY = new Color(Display.getCurrent(), new RGB(100, 100, 100));
	public final static Color VIOLET = new Color(Display.getCurrent(), new RGB(100, 0, 100));

}
