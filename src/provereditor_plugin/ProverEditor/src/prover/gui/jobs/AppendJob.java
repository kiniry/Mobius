package prover.gui.jobs;


import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.ui.progress.UIJob;

import prover.gui.ProverPresentation;
import prover.gui.editor.BasicTextAttribute;
import prover.gui.editor.IColorConstants;
import prover.gui.editor.LimitRuleScanner;

public class AppendJob extends UIJob implements IColorConstants {
	private StringBuffer strToAppend;
	private IDocument doc;
	private TextViewer tv;
	
	private ProverPresentation tp;
	private LimitRuleScanner scanner;
	private int oldlen;
	
	public AppendJob(LimitRuleScanner scanner, ProverPresentation tp) {
		super("Updating view");
		strToAppend = new StringBuffer();
		this.tp = (ProverPresentation)tp.clone();
		tv = tp.getTextViewer();
		doc = tv.getDocument();
		this.scanner = scanner;
		
	}
		
	public AppendJob(LimitRuleScanner scanner, ProverPresentation tp, String name ) {
		this(scanner, tp);
		add(name);
	}
	
	public AppendJob(ProverPresentation tp, String name) {
		this(null, tp);
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
		SimpleAppendJob saj = new SimpleAppendJob(tp);
		saj.add(strToAppend);
		oldlen = doc.getLength();
		saj.schedule();
//		try {
//			//saj.join();
//		} catch (InterruptedException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		schedule();
	}
	
	public IStatus runInUIThread(IProgressMonitor monitor) {

//		tv.setTopIndex(oldlen - 1);
		if(scanner != null) {
			//System.out.println(strToAppend);
			scanner.setRange(doc, oldlen, strToAppend.length());
			IToken tok;
			while (!(tok = scanner.nextToken()).isEOF()) {
				if(tok != scanner.getDefaultReturnToken()) {
					BasicTextAttribute bta = (BasicTextAttribute)tok.getData();
					tp.mergeStyleRange(new StyleRange(scanner.getTokenOffset(), 
							scanner.getTokenLength(), bta.getForeground(), 
							bta.getBackground()));
					
				}
				
			}
		}	
		tv.changeTextPresentation(tp, true);
			
		return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
	}
	
}