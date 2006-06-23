package umbra;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * @author Generated automatically
 */

public class ColorManager {

    /**
     * TODO write description
     */
    protected Map fColorTable = new HashMap(10);

    /**
     * TODO write description
     */
    public void dispose() {
		Iterator e = fColorTable.values().iterator();
		while (e.hasNext())
			 ((Color) e.next()).dispose();
	}

    /**
     * TODO write description
     * 
     * @param rgb TODO write description
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
