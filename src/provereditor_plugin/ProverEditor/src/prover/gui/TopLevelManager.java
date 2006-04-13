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
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import prover.Prover;
import prover.ProverEditorPlugin;
import prover.exec.AProverException;
import prover.exec.ITopLevel;
import prover.exec.toplevel.TopLevel;
import prover.exec.toplevel.stream.IStreamListener;
import prover.gui.editor.BasicPresentationReconciler;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.IColorConstants;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.jobs.AppendJob;
import prover.gui.jobs.ColorAppendJob;
import prover.plugins.AProverTranslator;
import prover.preference.PreferencePage;

public class TopLevelManager extends ViewPart implements IStreamListener, IColorConstants {
	private static TopLevelManager instance;
	private final static String GREETINGS = "This is ProverEditor version " + 
				ProverEditorPlugin.MAJORVERSION + "." + ProverEditorPlugin.VERSION + "." + ProverEditorPlugin.SUBVERSION +" !\n"; 
	
	
		
	private ProverFileContext fOldPc = ProverFileContext.empty;
	private TopLevel fTopLevel;
	private AProverTranslator fTranslator;

	private boolean fLock = false;
	private LimitRuleScanner fScanner;
	private BasicRuleScanner fParser;
	private Stack fParsedList = new Stack();
	private Prover fProver;

	private TextViewer tv;
	private IDocument fDocView;	
	private ProverPresentation fPresentation;
	
	public TopLevelManager() {
		super();
		instance = this;
	}
	public static TopLevelManager getInstance() {
		return instance;
	}
	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.toplevel.stream.IStreamListener#append(int, java.lang.String)
	 */
	public void append(int type, String str) {
		append(str);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {
		tv = new TextViewer(parent, SWT.V_SCROLL);
		tv.setEditable(false);
		
		if (fDocView == null) {
			fDocView = new Document("");
		}
		
		tv.setDocument(fDocView);
		fPresentation = new ProverPresentation(tv);

		new ColorAppendJob(fPresentation, GREETINGS, VIOLET).prepare();

	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPart#setFocus()
	 */
	public void setFocus() {}
	
	
	

	
	
	protected synchronized boolean lock() {
		if(fLock)
			return false;
		fLock = true; return true;
	}
	protected synchronized void unlock() {
		fLock = false;
	}
	
	

	
	public boolean progress(ProverFileContext pc) {
		if(!lock())
			return true;
		boolean b = progress_intern(pc);
		unlock();
		return b;
	}
	
	protected boolean progress_intern (ProverFileContext pc) {
		if(isNewDoc(pc))
			reset(pc);
		int oldlimit =pc.scan.getLimit();
		return progress_intern(pc, oldlimit, oldlimit);
	}
	
	private boolean progress_intern (ProverFileContext pc, int realoldlimit, int oldlimit) { 
		fParser.setRange(pc.doc, oldlimit, pc.doc.getLength() - oldlimit);
		UpdateJob uj;
		IToken tok;
		do {
			tok = fParser.nextToken();
		} while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
		if(tok.isEOF()) {
			return false;
		}
			
		int newlimit = fParser.getTokenOffset() + fParser.getTokenLength() - 1;
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
			switch(fProver.getTopLevelTranslator().hasToSend(fTopLevel, pc.doc, cmd, oldlimit, newlimit)) {
				case ITopLevel.DONT_SKIP: {
					fTopLevel.clearBuffer();
					fTopLevel.sendCommand(cmd);
					if(fTopLevel.isAlive()) {
						fParsedList.push(new Integer(realoldlimit));
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
			pc.scan.setLimit(realoldlimit);
			uj = new UpdateJob(pc.sv.getPresentationReconciler(), newlimit);
			uj.schedule();
			return false;
		} 
		
		return true;
	}
	
	/**
	 * Reset the top level and the view with the context
	 * passed as a parameter.
	 * @see #reset()
	 * @param pc The prover context which we have to
	 * reset the view with
	 */
	public void reset(ProverFileContext pc) {
		if(pc.doc != null) {
			fOldPc = pc;
			reset();
		}
	}

	
	public boolean isNewDoc(ProverFileContext pc) {
		return pc.doc != fOldPc.doc;
	}

	
	public boolean regress(ProverFileContext pc) {
		if(!lock())
			return true;
		boolean b = regress_intern(pc);
		unlock();
		return b;
	}	
	
	protected boolean regress_intern(ProverFileContext pc) {
		if (isNewDoc(pc)) {
			reset(pc);
			return false;
		}
		
		int oldlimit = pc.scan.getLimit();
		if((oldlimit > 0) && (fParsedList.size() > 0)) {
			int newlimit = ((Integer) fParsedList.pop()).intValue();
			String cmd;
			try {
				cmd = pc.doc.get(newlimit, oldlimit - newlimit).trim();
			} catch (BadLocationException e) {
				// it should not happen
				System.err.println("TopLevel.regress_intern: " + e);
				return false;
			}
			switch(fProver.getTopLevelTranslator().hasToSkip(fTopLevel, pc.doc, cmd, newlimit, oldlimit)) {
				case ITopLevel.DONT_SKIP: {
					try {
						fTopLevel.undo();
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
	

	
	/**
	 * Tries to respawn the top level. 
	 * First stop the toplevel if it is running, and after start it again.
	 */
	public void respawn() {
		fTopLevel.stop();
		Job job = new Job("Toplevel Starting") {

			protected IStatus run(IProgressMonitor monitor) {
				fDocView = new Document("");
				new UIJob("Updating Toplevel monitor") {

					public IStatus runInUIThread(IProgressMonitor monitor) {
						tv.setDocument(fDocView);
						fPresentation = new ProverPresentation(tv);
						
						tv.changeTextPresentation(fPresentation, true);
						new ColorAppendJob(fPresentation, GREETINGS, VIOLET).prepare();
						return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
					}
					
				}.schedule();
				
				reset(fOldPc);
				return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
			}
			
		};
		job.schedule();
		
	}
	
	/**
	 * Reset the view, reset the toplevel, and set up everything.
	 */
	private synchronized void reset() {
		if(fTopLevel != null) {
			fTopLevel.stop();
		}
		IEditorInput input = fOldPc.ce.getEditorInput();
		
		IFile path= (input instanceof IFileEditorInput) ? ((IFileEditorInput) input).getFile() : null;
		fProver = Prover.findProverFromFile(path.getRawLocation().toString());
		fTranslator = fProver.getTranslator();
	    fScanner = new LimitRuleScanner(fTranslator.getProofRules());
	    fParser = new BasicRuleScanner(fTranslator.getParsingRules());
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
			
			fTopLevel = new TopLevel(fProver.getName(), tab);
			fTopLevel.addStreamListener(this);
		} catch (AProverException e) {
			new ColorAppendJob(fPresentation, e.toString(), RED).prepare();
		}
	
		// we reset the view
		fOldPc.scan.setLimit(0);
		new UpdateJob(fOldPc.sv.getPresentationReconciler()).schedule();
	}

	
	public void append(String str) {
		int ind = 0;
		if((ind = str.indexOf("\n\n\n")) != -1) {
			append(str.substring(0, ind));
			str = str.substring(ind);
		}
		
		String [][] unicodeReplacements = fTranslator.getUnicodeReplacements();
		
		if(isUnicodeMode()) {
			for(int i =0; i < unicodeReplacements.length; i++) {
				str = str.replaceAll(unicodeReplacements[i][0], 
						unicodeReplacements[i][1]);
			}
		}
		String [][] replacements = fTranslator.getReplacements();
		for(int i =0; i < replacements.length; i++) {
			str = str.replaceAll(replacements[i][0], 
					replacements[i][1]);
		}
		AppendJob job = new AppendJob(fScanner, fPresentation);
		
	
		job.add(str);
		job.prepare();
	}


	/**
	 * Tell whether or not we shall use unicode characters.
	 * @return True if the unicode checkbox in the preferences is checked.
	 */
	public boolean isUnicodeMode() {
		return PreferencePage.getProverIsUnicode();
	}

	

	/**
	 * Tries to send a Ctrl-Break command to the prover.
	 * @see prover.exec.TopLevel#doBreak()
	 */
	public void doBreak() {
		try {
			if(fTopLevel != null)
				fTopLevel.doBreak();
		} catch (AProverException e) { }
	}
	

	/**
	 * The class UpdateJob is used to update the view once it has changed
	 * internally.
	 * @author J. Charles
	 */
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
		
		
		/*
		 *  (non-Javadoc)
		 * @see org.eclipse.ui.progress.UIJob#runInUIThread(org.eclipse.core.runtime.IProgressMonitor)
		 */
		public IStatus runInUIThread(IProgressMonitor monitor) {
			scan.everythingHasChanged(0/*oldlimit*/, newlimit); 
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		}
		
	}	
}
