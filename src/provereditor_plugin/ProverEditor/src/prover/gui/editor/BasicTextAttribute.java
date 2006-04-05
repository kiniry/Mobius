package prover.gui.editor;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.swt.graphics.Color;

public class BasicTextAttribute extends TextAttribute {

	private Color back = null;
	public BasicTextAttribute(Color foreground) {
		super(foreground);
		back = super.getBackground();
	}
	public void setBackground(Color bg) {
		back = bg;
	}
	
	public Color getBackground() {
		return back;
	}
}
