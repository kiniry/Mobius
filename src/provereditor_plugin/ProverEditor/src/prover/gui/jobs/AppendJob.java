package prover.gui.jobs;


import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.progress.UIJob;

import prover.gui.ProverPresentation;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.editor.BasicTextAttribute;
import prover.gui.editor.IColorConstants;

public class AppendJob extends UIJob implements IColorConstants {
	private StringBuffer strToAppend;
	private IDocument doc;
	private TextViewer tv;
	
	private ProverPresentation tp;
	private LimitRuleScanner scanner;
	
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
	
	public AppendJob(ProverPresentation tp, String name, Color col) {
		this(null, tp);
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
			System.err.println("ProverEditor: AppendJob.addColor, Wrong length !");
			System.err.println("ProverEditor: Recovering...");
			len = strToAppend.length() - (offset + 1); 
		}
		
		tp.mergeStyleRange(new StyleRange(offset + doc.getLength(), len, col, WHITE));
		
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
		if(scanner != null) {
			//System.out.println(strToAppend);
			scanner.setRange(doc, len, strToAppend.length());
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