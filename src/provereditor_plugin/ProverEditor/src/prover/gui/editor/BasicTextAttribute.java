package prover.gui.editor;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.swt.graphics.Color;


/**
 * A text attribute class with enhanced background color support.
 */
public class BasicTextAttribute extends TextAttribute {
	/** the background color */
	private Color fBgColor = null;
	
	/**
	 * Create a text attribute with the specified foreground color.
	 * @param foreground A color. Cannot be <code>null</code>
	 */
	public BasicTextAttribute(Color foreground) {
		super(foreground);
		fBgColor = super.getBackground();
	}
	
	/**
	 * Change the background color of the text attribute
	 * @param bgColor the new background color
	 */
	public void setBackground(Color bgColor) {
		fBgColor = bgColor;
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.TextAttribute#getBackground()
	 */
	public Color getBackground() {
		return fBgColor;
	}
}
