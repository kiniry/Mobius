package ie.ucd.bon.plugin.editor;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

public final class BONColourProvider {

	public static final RGB SINGLE_LINE_COMMENT= new RGB(128, 128, 0);
	public static final RGB KEYWORD= new RGB(0, 0, 128);
	public static final RGB STRING= new RGB(0, 128, 0);
	public static final RGB DEFAULT= new RGB(0, 0, 0);

	protected Map<RGB, Color> colourTable= new HashMap<RGB, Color>(10);

	/**
	 * Release all of the color resources held onto by the receiver.
	 */	
	public void dispose() {
		for (Color colour : colourTable.values()) {
			colour.dispose();
		}
	}
	
	/**
	 * Return the color that is stored in the color table under the given RGB
	 * value.
	 * 
	 * @param rgb the RGB value
	 * @return the color stored in the color table for the given RGB value
	 */
	public Color getColour(RGB rgb) {
		Color colour= colourTable.get(rgb);
		if (colour == null) {
			colour= new Color(Display.getCurrent(), rgb);
			colourTable.put(rgb, colour);
		}
		return colour;
	}
	
}
