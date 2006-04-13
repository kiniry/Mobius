package prover.gui.jobs;


import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.ui.progress.UIJob;

import prover.gui.editor.IColorConstants;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.editor.BasicTextPresentation;

public class SimpleAppendJob extends UIJob implements IColorConstants {
	private StringBuffer strToAppend;
	private IDocument doc;
	private TextViewer tv;
	
	
	public SimpleAppendJob(BasicTextPresentation tp) {
		super("Updating view");
		strToAppend = new StringBuffer();
//		this.tp = (ProverPresentation)tp.clone();
		tv = tp.getTextViewer();
		doc = tv.getDocument();
		
	}
		
	public SimpleAppendJob(LimitRuleScanner scanner, BasicTextPresentation tp, String name ) {
		this(tp);
		add(name);
	}
	
	public SimpleAppendJob(BasicTextPresentation tp, String name) {
		this(tp);
	}
	public void add(StringBuffer str) {
		strToAppend.append(str);
	}
	
	public void add(String str) {
		add(new StringBuffer(str));
	}

	public int getLength() {
		return strToAppend.length();
	}
	
	
	public void prepare() {
		
		schedule();
	}
	
	public IStatus runInUIThread(IProgressMonitor monitor) {
		int len = doc.getLength();
		try {
			doc.replace(len, 0, strToAppend.toString());
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		tv.setTopIndex(len - 1);
//		tv.changeTextPresentation(tp, true);
			
		return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
	}
	
}