package prover.gui.editor;

import java.util.Iterator;

import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.swt.custom.StyleRange;

public class BasicTextPresentation extends TextPresentation {
	private TextViewer tv;
	
	public BasicTextPresentation(TextViewer tv) {
		super();
		this.tv = tv;
	}
	
	public BasicTextPresentation(BasicTextPresentation pres) {
		super();
		Iterator iter = pres.getAllStyleRangeIterator();
		while(iter.hasNext()) {
			this.addStyleRange((StyleRange) ((StyleRange)iter.next()).clone());
		}
		this.setDefaultStyleRange(pres.getDefaultStyleRange());
		this.tv = pres.tv;
	}

	public TextViewer getTextViewer() {
		return tv;
	}
	
	public Object clone() {
		return new BasicTextPresentation(this);
	}
	
}
