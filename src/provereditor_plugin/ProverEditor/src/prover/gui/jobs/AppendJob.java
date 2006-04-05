package prover.gui.jobs;


import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.progress.UIJob;

import prover.gui.ProverPresentation;
import prover.gui.editor.IColorConstants;

public class AppendJob extends UIJob implements IColorConstants {
	private StringBuffer strToAppend;
	private IDocument doc;
	private TextViewer tv;
	
	private ProverPresentation tp;
	
	public AppendJob(ProverPresentation tp) {
		super("Updating view");
		strToAppend = new StringBuffer();
		this.tp = (ProverPresentation)tp.clone();
		tv = tp.getTextViewer();
		doc = tv.getDocument();
	}
		
	public AppendJob(ProverPresentation tp, String name ) {
		this(tp);
		add(name);
	}
	
	public AppendJob(ProverPresentation tp, String name, Color col) {
		this(tp);
		add(name, col);
	}
	public void add(StringBuffer str) {
		strToAppend.append(str);
	}
	
	public void add(String str) {
		add(new StringBuffer(str));
	}
	public void add(StringBuffer str, Color col) {
		int ol = strToAppend.length();
		strToAppend.append(str);
		addColor(ol, str.length() - 1, col);
	}
	public void add(String str, Color col) {
		add(new StringBuffer(str), col);
	}
	public int getLength() {
		return strToAppend.length();
	}
	public void addColor(int offset, int len, Color col)  {
		if (offset >= strToAppend.length()) // out of bounds
			throw new IllegalArgumentException("AppendJob.addColor: Wrong offset !");
		if (offset + len >= strToAppend.length()) { // out of bounds
			System.err.println("CoqEditor: AppendJob.addColor, Wrong length !");
			System.err.println("CoqEditor: Recovering...");
			len = strToAppend.length() - (offset + 1); 
		}
		
		
		
//		if(realoffset + len >= dc.getLength() + strToAppend.length()) {
//			len = ((dc.getLength() + strToAppend.length()) - (realoffset)); 
//		}
		
		tp.mergeStyleRange(new StyleRange(offset + doc.getLength(), len, col, WHITE));
		
	}
	public IStatus runInUIThread(IProgressMonitor monitor) {
		try {
			doc.replace(doc.getLength(), 0, strToAppend.toString());
			
			tv.setTopIndex(doc.getLength() - 1);
			tv.changeTextPresentation(tp, true);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
	}
	
}