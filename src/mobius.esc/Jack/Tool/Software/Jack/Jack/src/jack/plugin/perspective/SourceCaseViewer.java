//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/

package jack.plugin.perspective;

import jack.plugin.JackPlugin;
import jack.plugin.edit.JavaLineStyler;
import jack.plugin.edit.JavaScanner;
import jack.plugin.edit.bc.BCScanner;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Enumeration;

import jpov.JpoFile;
import jpov.viewer.source.Box;
import jpov.viewer.tree.TreeItemSelection;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.jface.text.source.VerticalRuler;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.actions.ActionFactory;
import org.eclipse.ui.part.ViewPart;

/**
 * View that displays the source.
 * 
 * @author L. Burdy
 */
public class SourceCaseViewer extends ViewPart implements ISourceCaseViewer {

	SourceViewer sourceView;
	JavaLineStyler lineStyler;
	MySourceViewerConfiguration msvc;

	public void createPartControl(Composite parent) {
		lineStyler = new JavaLineStyler(new JavaScanner());
		sourceView = new SourceViewer(parent, new VerticalRuler(5),
				SWT.V_SCROLL | SWT.H_SCROLL | SWT.BORDER);
		sourceView.setEditable(false);
		msvc = new MySourceViewerConfiguration(this);
		sourceView.configure(msvc);
		sourceView.getTextWidget().addLineStyleListener(lineStyler);
		sourceView.getTextWidget().setFont(
			new Font(getViewSite().getShell().getDisplay(), JackPlugin
					.getViewerFont()));

		CopyAction copyAction = new CopyAction(sourceView);
		getViewSite().getActionBars().setGlobalActionHandler(
			ActionFactory.COPY.getId(), copyAction);
	}

	public void setFocus() {
	}

	void setDocument(IFile f, TreeItemSelection ehl) {
		lineStyler.setScanner(new JavaScanner());
		StringBuffer s = new StringBuffer();
		try {
			BufferedInputStream stream = new BufferedInputStream(f
					.getContents());
			int a;
			while ((a = stream.available()) != 0) {
				byte[] ba = new byte[a];
				stream.read(ba, 0, a);
				s.append(new String(ba));
			}
		} catch (IOException ioe) {
			;
		} catch (CoreException ce) {
			;
		}
		sourceView.setDocument(new Document(s.toString()));
		msvc.setEhl(ehl);
//		lineStyler = new JavaLineStyler(new JavaScanner());
		lineStyler.parseBlockComments(s.toString());
	}

	void setDocument(File classFile) {
		lineStyler.setScanner(new BCScanner());
		StringBuffer s = new StringBuffer();
		try {
			BufferedInputStream stream = new BufferedInputStream(new FileInputStream(classFile));
			int a;
			while ((a = stream.available()) != 0) {
				byte[] ba = new byte[a];
				stream.read(ba, 0, a);
				s.append(new String(ba));
			}
		} catch (IOException ioe) {
			;
		}
		sourceView.setDocument(new Document(s.toString()));
//		msvc.setEhl(ehl);
//		lineStyler = new JavaLineStyler(new BCScanner());
		lineStyler.parseBlockComments(s.toString());
	}

	void updateTitle(JpoFile jpoFile) {
		String title = "Case Viewer - ";
		int nbPo = jpoFile.getJmlFile().getNbPo();
		int proved = jpoFile.getJmlFile().getNbPoProved();
		int checked = jpoFile.getJmlFile().getNbCheckedPo();
		title += "Lemma: " + nbPo + " - Proved: " + proved + " ("
				+ (nbPo == 0 ? 100 : ((proved * 100) / nbPo)) + "%)"
				+ " - Checked: " + checked + " ("
				+ (nbPo == 0 ? 100 : ((checked * 100) / nbPo)) + "%)";
		setPartName(title);
	}

	public void setTopIndex(int line) {
		sourceView.setTopIndex(line);
		sourceView.getControl().redraw();
	}

	public boolean highlight(Color fgcolor, Color bgcolor, int line,
			int column, int length) {
		try {
			if (sourceView.getDocument() != null)
				lineStyler.addBox(fgcolor, bgcolor, sourceView.getDocument()
						.getLineOffset(line)
						+ column, length);
		} catch (BadLocationException ble) {
			return false;
		}
		return true;
	}

	public void eraseColor() {
		lineStyler.clearBoxes();
		sourceView.getTextWidget().redraw();
	}

}

/**
 * This action allows to copy a selected part of the source?.
 * 
 * @author L. Burdy
 */
class CopyAction extends Action {

	SourceViewer sourceV;

	CopyAction(SourceViewer sv) {
		sourceV = sv;
	}

	public void run() {
		sourceV.getTextWidget().copy();
	}
}

/**
 * This class implements a text hover displayer to display informations
 * associated to red and blue colored text.
 * 
 * @author L. Burdy
 */
class SourceHover implements ITextHover {

	private SourceViewer ew;

	//	private SourceCaseViewer scv;

	private TreeItemSelection ehl;

	SourceHover(SourceCaseViewer s, SourceViewer v) {
		ew = v;
		//		scv = s;
	}

	void setEhl(TreeItemSelection ehl) {
		this.ehl = ehl;
	}

	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		if (ehl != null) {
			String text = null;
			Enumeration en = ehl.getLabels();
			while (en.hasMoreElements()) {
				Box b = (Box) en.nextElement();
				if (b.in(ew.getTextWidget(), offset))
					if (text == null)
						text = b.getCommentText();
					else
						text += "\n-------------\n" + b.getCommentText();
			}
			if (text != null)
				return new MyRegion(text, offset);

		}
		return new Region(offset, 0);
	}

	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		if (hoverRegion instanceof MyRegion)
			return ((MyRegion) hoverRegion).getText();
		else
			return null;
	}

}

/**
 * This class defines a region in the displayed text.
 * 
 * @author L. Burdy
 */
class MyRegion implements IRegion {

	String text;
	int off;

	MyRegion(String r, int offset) {
		text = r;
		off = offset;
	}

	public int getLength() {
		return text.length();
	}

	public int getOffset() {
		return off;
	}

	/**
	 * @return
	 */
	public String getText() {
		return text;
	}

}

/**
 * This class implements a source viewer configuration that allows to associate
 * a text hover displayer to the source viewer.
 * 
 * @author L. Burdy
 */
class MySourceViewerConfiguration extends SourceViewerConfiguration {

	private SourceCaseViewer s;
	private SourceHover sh;

	MySourceViewerConfiguration(SourceCaseViewer scv) {
		s = scv;
	}

	void setEhl(TreeItemSelection ehl) {
		if (sh != null)
			sh.setEhl(ehl);
	}

	public ITextHover getTextHover(ISourceViewer sourceViewer,
			String contentType) {
		sh = new SourceHover(s, (SourceViewer) sourceViewer);
		return sh;
	}
}