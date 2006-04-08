package prover.gui;

import java.util.Stack;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import prover.AProverTranslator;
import prover.Prover;
import prover.ProverEditorPlugin;
import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.exec.toplevel.stream.IStreamListener;
import prover.gui.editor.BasicPresentationReconciler;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.IColorConstants;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.editor.ProverEditor;
import prover.gui.jobs.AppendJob;
import prover.gui.jobs.ColorAppendJob;
import prover.preference.PreferencePage;

public class TopLevelManager extends ViewPart implements IStreamListener, IColorConstants {
	private IDocument dc;	
	
	private ProverContext oldpc = ProverContext.empty;
	private ITopLevel top;
	private TextViewer tv;
	private ProverPresentation tp;
	private final static String GREETINGS = "This is ProverEditor version " + 
			ProverEditorPlugin.MAJORVERSION + "." + ProverEditorPlugin.VERSION + "." + ProverEditorPlugin.SUBVERSION +" !\n"; 
	
	AProverTranslator translator;
	
	private static TopLevelManager instance;
	
	private boolean bLock = false;

	private String msg;
	private LimitRuleScanner scanner;
	private BasicRuleScanner parser;
	private Stack parsedList = new Stack();
	
	public TopLevelManager() {
		super();
		instance = this;
	}
	public static TopLevelManager getInstance() {
		return instance;
	}
	public void append(String str) {
		append(str, translator);
	}
	public void append(int type, String str) {
		append(str, translator);
	}
	
	public void createPartControl(Composite parent) {
		tv = new TextViewer(parent, SWT.V_SCROLL);
		tv.setEditable(false);
		
		if (dc == null) {
			dc = new Document("");
		}
		
		tv.setDocument(dc);
		tp = new ProverPresentation(tv);

		new ColorAppendJob(tp, GREETINGS, VIOLET).prepare();

	}

	
	public void setFocus() {}
	
	
	

	protected synchronized boolean lock() {
		if(bLock)
			return false;
		bLock = true; return true;
	}
	protected synchronized void unlock() {
		bLock = false;
	}
	
	
	protected boolean progress_intern (ProverContext pc) {
		if(isNewDoc(pc))
			reset(pc);
		int oldlimit =pc.scan.getLimit();
		return progress_intern(pc, oldlimit, oldlimit);
	}
	
	
	private boolean progress_intern (ProverContext pc, int realoldlimit, int oldlimit) { 
		parser.setRange(pc.doc, oldlimit, pc.doc.getLength() - oldlimit);
		UpdateJob uj;
		IToken tok;
		do {
			tok = parser.nextToken();
		} while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
		if(tok.isEOF()) {
			return false;
		}
			
		int newlimit = parser.getTokenOffset() + parser.getTokenLength() - 1;
		try {
			String cmd;
			try {
				cmd = pc.doc.get(realoldlimit, newlimit - oldlimit).trim();
			} catch (BadLocationException e) {
				// it should not happen
				System.err.println("TopLevel.progress_intern: " + e);
				return false;
			}
			
			// first we lock the evaluated part
			pc.scan.setLimit(newlimit);
			uj = new UpdateJob(pc.sv.getPresentationReconciler(), newlimit);
			uj.schedule();
			
			
			//we send the command
			switch(top.hasToSend(pc.doc, cmd, oldlimit, newlimit)) {
				case ITopLevel.DONT_SKIP: {
					top.clearBuffer();
					top.sendCommand(cmd);
					if(top.isAlive()) {
						msg = top.getStdBuffer();
						parsedList.push(new Integer(realoldlimit));
					}
					else {
						pc.scan.setLimit(realoldlimit);
						uj = new UpdateJob(pc.sv.getPresentationReconciler(), newlimit);
						uj.schedule();
						return false;
					}
					break;
				}
				case ITopLevel.SKIP: 
					break;
				case ITopLevel.SKIP_AND_CONTINUE: {
					progress_intern(pc, realoldlimit, newlimit);
					break;
				}
			}
		} catch (AProverException e) {
			msg = e + top.getStdBuffer();
			pc.scan.setLimit(realoldlimit);
			uj = new UpdateJob(pc.sv.getPresentationReconciler(), newlimit);
			uj.schedule();
			return false;
		} 
		
		return true;
	}
	

	public void reset(ProverContext pc) {
		if(pc.doc != null) {
			oldpc = pc;
			reset();
		}
	}

	private boolean isNewDoc(ProverContext pc) {
		return pc.doc != oldpc.doc;
	}

	public String getMsg() {
		return msg;
	}
	
	
	protected boolean regress_intern(ProverContext pc) {
		if (isNewDoc(pc)) {
			reset(pc);
			return false;
		}
		
		int oldlimit = pc.scan.getLimit();
		if((oldlimit > 0) && (parsedList.size() > 0)) {
			int newlimit = ((Integer) parsedList.pop()).intValue();
			String cmd;
			try {
				cmd = pc.doc.get(newlimit, oldlimit - newlimit).trim();
			} catch (BadLocationException e) {
				// it should not happen
				System.err.println("TopLevel.regress_intern: " + e);
				return false;
			}
			switch(top.hasToSkip(pc.doc, cmd, newlimit, oldlimit)) {
				case ITopLevel.DONT_SKIP: {
					try {
						top.undo();
					} catch (AProverException e) {
						append(e.toString());
					}
					pc.scan.setLimit(newlimit);
					break;
				}
				case ITopLevel.SKIP: {
					pc.scan.setLimit(newlimit);
					break;
				}
				case ITopLevel.SKIP_AND_CONTINUE: {
					pc.scan.setLimit(newlimit);
					regress_intern(pc);
					break;
				}
				
			}
			
			
			UpdateJob uj = new UpdateJob(pc.sv.getPresentationReconciler(), oldlimit + 1);
			uj.schedule();
		}
		return true;
	}
	public boolean progress(ProverEditor ce, IDocument doc, FindReplaceDocumentAdapter fda, BasicSourceViewerConfig sv, LimitRuleScanner scan) {
		if(!lock())
			return true;
		boolean b = progress_intern(new ProverContext(ce, doc, sv, scan));
		unlock();
		return b;
	}
	
	public boolean regress(ProverEditor ce, IDocument doc, FindReplaceDocumentAdapter fda, BasicSourceViewerConfig sv, LimitRuleScanner scan) {
		if(!lock())
			return true;
		boolean b = regress_intern(new ProverContext(ce, doc, sv, scan));
		unlock();
		return b;
	}
	
	
	
	public void respawn() {
		top.stop();
		Job job = new Job("Toplevel Starting") {

			protected IStatus run(IProgressMonitor monitor) {
				dc = new Document("");
				new UIJob("Updating Toplevel monitor") {

					public IStatus runInUIThread(IProgressMonitor monitor) {
						tv.setDocument(dc);
						tp = new ProverPresentation(tv);
						
						tv.changeTextPresentation(tp, true);
						new ColorAppendJob(tp, GREETINGS, VIOLET).prepare();
						return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
					}
					
				}.schedule();
				
				reset(oldpc);
				return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
			}
			
		};
		job.schedule();
		
	}
	
	private synchronized void reset() {
		if(top != null) {
			top.stop();
		}
		IEditorInput input = oldpc.ce.getEditorInput();
		
		IFile path= (input instanceof IFileEditorInput) ? ((IFileEditorInput) input).getFile() : null;
	    translator = Prover.findProverFromFile(path.getRawLocation().toString()).getTranslator();
	    scanner = new LimitRuleScanner(translator.getProofRules());
	    parser = new BasicRuleScanner(translator.getParsingRules());
		String [] tab = null;
		
		if(path != null) {
			if(path.getParent().getRawLocation() == null) {
				tab = new String [0];
			}
			else {
				tab = new String [1];
				tab[0] = path.getParent().getRawLocation().toString();
			}
		}
		try {
			
			top = translator.createNewTopLevel(tab);
			top.addStreamListener(this);
		} catch (AProverException e) {
			new ColorAppendJob(tp, e.toString(), RED).prepare();
		}
		
		//System.out.println(oldce.getSite());
		resetView();
	}
	
	protected synchronized void resetView() {
		if(oldpc != null) {
			oldpc.scan.setLimit(0);
			new UpdateJob(oldpc.sv.getPresentationReconciler()).schedule();
		}
	}

	public void printMsg() {
		//dc.set(msg);
	}
	
	
	
	
	public void append(String str, AProverTranslator translator) {
		int ind = 0;
		if((ind = str.indexOf("\n\n\n")) != -1) {
			append(str.substring(0, ind));
			str = str.substring(ind);
		}
		
		String [][] unicodeReplacements = translator.getUnicodeReplacements();
		
		if(isUnicodeMode()) {
			for(int i =0; i < unicodeReplacements.length; i++) {
				str = str.replaceAll(unicodeReplacements[i][0], 
						unicodeReplacements[i][1]);
			}
		}
		String [][] replacements = translator.getReplacements();
		for(int i =0; i < replacements.length; i++) {
			str = str.replaceAll(replacements[i][0], 
					replacements[i][1]);
		}
		AppendJob job = new AppendJob(scanner, tp);
		
	
		job.add(str);
		job.prepare();
	}


	
	public boolean isUnicodeMode() {
		return PreferencePage.getProverIsUnicode();
	}




	

	private class UpdateJob extends UIJob {
		private int newlimit;
		private BasicPresentationReconciler scan;
		public UpdateJob(BasicPresentationReconciler sc, int limit) {
			super("Updating text");
			scan = sc;
			this.newlimit = limit;
		}

		public UpdateJob(BasicPresentationReconciler sc) {
			this(sc, sc.getDocument().getLength());
		}

		public IStatus runInUIThread(IProgressMonitor monitor) {
			
			scan.everythingHasChanged(0/*oldlimit*/, newlimit); 
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		}
		
	}


	public void doBreak() {
		try {
			if(top != null)
				top.doBreak();
		} catch (AProverException e) {
			//e.printStackTrace();
		}
	}
	
}
