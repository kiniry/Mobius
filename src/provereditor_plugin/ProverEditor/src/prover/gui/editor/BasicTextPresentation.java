package prover.gui.editor;

import java.util.Iterator;

import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.swt.custom.StyleRange;

/**
 * This class is just the same as the normal text presentation
 * class, but some useful methods are added.
 * @see TextPresentation
 */
public class BasicTextPresentation extends TextPresentation {
	/** the viewer associated with the text presentation */
	private TextViewer fViewer;
	
	/**
	 * Construct a text presentation associated with the specified
	 * viewer.
	 * @param viewer a text viewer, cannot be null.
	 */
	public BasicTextPresentation(TextViewer viewer) {
		super();
		fViewer = viewer;
	}
	
	/**
	 * A copy constructor.
	 * @param pres the presentation to be the copy of.
	 */
	public BasicTextPresentation(BasicTextPresentation pres) {
		super();
		Iterator iter = pres.getAllStyleRangeIterator();
		while(iter.hasNext()) {
			this.addStyleRange((StyleRange) ((StyleRange)iter.next()).clone());
		}
		this.setDefaultStyleRange(pres.getDefaultStyleRange());
		fViewer = pres.fViewer;
	}

	/**
	 * Returns the current text viewer associated with the presentation.
	 * @return a text viewer (shall not be null)
	 */
	public TextViewer getTextViewer() {
		return fViewer;
	}
	
	/*
	 *  (non-Javadoc)
	 * @see java.lang.Object#clone()
	 */
	public Object clone() {
		return new BasicTextPresentation(this);
	}
	
}
