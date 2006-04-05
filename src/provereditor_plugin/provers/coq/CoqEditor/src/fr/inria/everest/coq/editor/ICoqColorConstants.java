package fr.inria.everest.coq.editor;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

import prover.gui.editor.IColorConstants;

public interface ICoqColorConstants extends IColorConstants {
	
	// Colors...
	public final static Color TAG_COLOR = 
		new Color(Display.getCurrent(), new RGB(100, 0, 100));
	public final static Color STRING_COLOR = 
		new Color(Display.getCurrent(), new RGB(0, 0, 200));
	public final static Color COMMENT_COLOR = 
		new Color(Display.getCurrent(), new RGB(0, 100, 0));
	public final static Color LEMMA_COLOR = 
		new Color(Display.getCurrent(), new RGB(200, 30, 30));
	

}
