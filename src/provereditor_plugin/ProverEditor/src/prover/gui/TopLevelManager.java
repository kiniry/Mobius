package prover.gui;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
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
import prover.exec.toplevel.TopLevel;
import prover.exec.toplevel.stream.StreamHandler;
import prover.gui.editor.BasicPresentationReconciler;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicTextPresentation;
import prover.gui.editor.IColorConstants;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.jobs.AppendJob;
import prover.gui.jobs.ColorAppendJob;
import prover.gui.popup.AddToLoadPath;
import prover.gui.preference.PreferencePage;
import prover.plugins.AProverTranslator;
import prover.plugins.IProverTopLevel;

/**
 * The top level manager is the main class of the gui of ProverEditor.
 * It controls the top level, it glue the editor with the commands.
 * And it is a view part to show the current prover state.
 */
public class TopLevelManager extends ViewPart implements IColorConstants {
	/* Private fields: */
	/** the greetings message */
	public final static String GREETINGS = "This is ProverEditor version " + 
											ProverEditorPlugin.MAJORVERSION + "." + 
											ProverEditorPlugin.VERSION + "." + 
											ProverEditorPlugin.SUBVERSION +" !\n"; 	
	/** the current TopLevelManager instance */
	private static TopLevelManager instance;
	
	/* Instance fields: */
	/** the context associated with the current top level */
	private ProverFileContext fProverContext = ProverFileContext.empty;
	/** the current running top level */
	private TopLevel fTopLevel;
	/** the current prover running */
	private Prover fProver;
	/** the translator currently used */
	private AProverTranslator fTranslator;
	/** the parser used to parse the currently evaluated document */
	private BasicRuleScanner fParser;
	
	/** the lock system to avoid race conditions */
	private boolean fLock = false;
	/** the list of offset being the steps already taken by progress */
	private Stack fParsedList = new Stack();

	/* The text viewer used to show the prover state related fields: */
	/** the text viewer to show the state of the prover */
	private TextViewer fStateText;
	/** the current text presentation associated with the text viewer */
	private BasicTextPresentation fStatePres;
	/** the scanner used to color the text in the text viewer */
	private BasicRuleScanner fStateScan;
	
	
	/**
	 * Empty constructor. Creates an instance. There shall be only one
	 * instance of the top level manager.
	 */
	public TopLevelManager() {
		super();
		instance = this;
	}
	
	/**
	 * Returns the current instance of the top level manager.
	 * @return the last instance created of the top level manager.
	 */
	public static TopLevelManager getInstance() {
		return instance;
	}
	
	
	/*
	 *  (non-Javadoc)
	 * @see prover.exec.toplevel.stream.IStreamListener#append(int, java.lang.String)
	 */
	public void append(StreamHandler handler, String str) {
		append(str);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {
		IDocument doc = null;
		if (fStateText == null) {
			doc = new Document("");
		}
		else {
			doc = fStateText.getDocument();
		}
		fStateText = new TextViewer(parent, SWT.V_SCROLL);
		fStateText.setEditable(false);		
		fStateText.setDocument(doc);
		fStatePres = new BasicTextPresentation(fStateText);

		new ColorAppendJob(fStatePres, GREETINGS, VIOLET).prepare();

	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPart#setFocus()
	 */
	public void setFocus() {}
	
	
	

	
	/**
	 * Sets the lock.
	 * @return <code>true</code> if everything went well, 
	 *  <code>false</code> if the lock was already set.
	 */
	protected synchronized boolean lock() {
		if(fLock)
			return false;
		fLock = true; return true;
	}
	
	/**
	 * Unsets the lock.
	 */
	protected synchronized void unlock() {
		fLock = false;
	}
	
	

	/**
	 * Progress in the proof. If the progress was successful return true,
	 * otherwise returns false.
	 * @param pc the context in which to progress.
	 * @return true if the progress was successful, false otherwise or if the
	 *  lock was already set.
	 */
	public boolean progress(ProverFileContext pc) {
		if(!lock())
			return true;
		boolean res;
		if(isNewDoc(pc)) {
			reset(pc);
			res = false;
		}
		else {
			int oldlimit =pc.scan.getLimit();
			res = progress_intern(pc, oldlimit, oldlimit);
		}
		unlock();
		return res;
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
			switch(fProver.getTopLevelTranslator().hasToSkipSendCommand(fTopLevel, pc.doc, cmd, oldlimit, newlimit)) {
				case IProverTopLevel.DONT_SKIP: {
					fTopLevel.sendCommand(cmd);
					append(fTopLevel.getStdBuffer());
					if(fTopLevel.isAlive()) {
						fParsedList.push(new Integer(realoldlimit));
					}
					else {
						pc.scan.setLimit(oldlimit);
						uj = new UpdateJob(pc.sv.getPresentationReconciler(), newlimit);
						uj.schedule();
						return false;
					}
					break;
				}
				case IProverTopLevel.SKIP: 
					break;
				case IProverTopLevel.SKIP_AND_CONTINUE: {
					progress_intern(pc, realoldlimit, newlimit);
					break;
				}
			}
		} catch (AProverException e) {
			pc.scan.setLimit(realoldlimit);
			uj = new UpdateJob(pc.sv.getPresentationReconciler(), newlimit);
			uj.schedule();
			ColorAppendJob caj = new ColorAppendJob(fStatePres, e.toString(), RED);
			caj.prepare();
			return false;
		} 
		return true;
	}
	


	/**
	 * Regress in the proof. If the undo was successful returns true,
	 * otherwise returns false.
	 * @param pc the context in which to undo a command.
	 * @return true if the undo was successful, false otherwise or if the
	 *  lock was already set.
	 */
	public boolean regress(ProverFileContext pc) {
		if(!lock())
			return true;
		boolean res;
		if (isNewDoc(pc)) {
			reset(pc);
			res = false;
		}
		else {
			res = regress_intern(pc);
		}
		unlock();
		return res;
	}	
	
	protected boolean regress_intern(ProverFileContext pc) {
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
			switch(fProver.getTopLevelTranslator().hasToSkipUndo(fTopLevel, pc.doc, cmd, newlimit, oldlimit)) {
				case IProverTopLevel.DONT_SKIP: {
					try {
						fTopLevel.undo();
					} catch (AProverException e) {
						append(e.toString());
					}
					pc.scan.setLimit(newlimit);
					break;
				}
				case IProverTopLevel.SKIP: {
					pc.scan.setLimit(newlimit);
					break;
				}
				case IProverTopLevel.SKIP_AND_CONTINUE: {
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
	 * @deprecated
	 * Use {@link #reset(ProverFileContext)} instead.
	 */
	public void respawn() {
		fTopLevel.stop();
		Job job = new Job("Toplevel Starting") {

			protected IStatus run(IProgressMonitor monitor) {
				new UIJob("Updating Toplevel monitor") {

					public IStatus runInUIThread(IProgressMonitor monitor) {
						fStateText.setDocument(new Document(""));
						fStatePres = new BasicTextPresentation(fStateText);
						
						fStateText.changeTextPresentation(fStatePres, true);
						new ColorAppendJob(fStatePres, GREETINGS, VIOLET).prepare();
						return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
					}
					
				}.schedule();
				
				reset(fProverContext);
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
		IEditorInput input = fProverContext.ce.getEditorInput();
		
		IFile path= (input instanceof IFileEditorInput) ? ((IFileEditorInput) input).getFile() : null;
		fProver = Prover.findProverFromFile(path.getRawLocation().toString());
		fTranslator = fProver.getTranslator();
	    fStateScan = new LimitRuleScanner(fTranslator.getProverStateRules());
	    fParser = new BasicRuleScanner(fTranslator.getParsingRules());
		String [] tab = null;
		
		if(path != null) {
			
//			if(path.getParent().getRawLocation() == null) {
//				tab = new String [0];
//			}
//			else {
//				tab = new String [1];
//				tab[0] = path.getParent().getRawLocation().toString();
//			}
			HashSet hsPath;
			try {
				hsPath = AddToLoadPath.getPaths(path.getProject().getLocation().toString());
			} catch (IOException e) {
				hsPath = new HashSet();
			}
			tab = new String[hsPath.size() + 2];
			tab [0]= path.getProject().getLocation().toString();
			tab [1] = path.getLocation().removeLastSegments(1).toString();
			Iterator iter = hsPath.iterator();
			for(int i = 2; i < tab.length; i++) {
				tab[i] = tab[0] + File.separator + iter.next().toString();
			}

		}
		new ColorAppendJob(fStatePres, "\nEditing file: \n" + path.getName() + "\n", DARKRED).prepare();
		
		try {
			
			fTopLevel = new TopLevel(fProver.getName(), tab);
			//fTopLevel.addStandardStreamListener(this);
		} catch (AProverException e) {
			new ColorAppendJob(fStatePres, e.toString(), RED).prepare();
		}
	
		// we reset the view
		fProverContext.scan.setLimit(0);
		new UpdateJob(fProverContext.sv.getPresentationReconciler()).schedule();
	}

	
	/**
	 * Add the string given as an argument to the text viewer
	 * used to show the state of the prover.
	 * @param str The string to add to the text viewer of the prover.
	 */
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
		AppendJob job = new AppendJob(fStateScan, fStatePres);
		
	
		job.add(str);
		job.prepare();
	}

	
	/**
	 * Reset the top level and the view with the context
	 * passed as a parameter.
	 * @param pc The prover context which we have to
	 * reset the view with
	 */
	public void reset(ProverFileContext pc) {
		if(pc.doc != null) {
			fProverContext = pc;
			reset();
		}
	}

	/**
	 * Tells whether or not the current doc
	 * is the same as the doc in the context given as a parameter.
	 * @param pc The context to test
	 * @return true if the documents are different.
	 */
	public boolean isNewDoc(ProverFileContext pc) {
		return pc.doc != fProverContext.doc;
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
	 * @see prover.exec.ITopLevel#doBreak()
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
	
	 */
	private class UpdateJob extends UIJob {
		/** the limit of the update */
		private int fLimit;
		/** the presentation reconciler to update */
		private BasicPresentationReconciler fReconciler;
		
		/**
		 * Create a job to update a presentation reconciler in a UIThread context.
		 * @param reconciler The reconciler to update.
		 * @param limit The limit of the update.
		 */
		public UpdateJob(BasicPresentationReconciler reconciler, int limit) {
			super("Updating text");
			fReconciler = reconciler;
			fLimit = limit;
		}

		/**
		 * Create a job to update a presentation reconciler in a UIThread context.
		 * @param reconciler The reconciler to update.
		 */
		public UpdateJob(BasicPresentationReconciler reconciler) {
			this(reconciler, reconciler.getDocument().getLength());
		}
		
		
		/*
		 *  (non-Javadoc)
		 * @see org.eclipse.ui.progress.UIJob#runInUIThread(org.eclipse.core.runtime.IProgressMonitor)
		 */
		public IStatus runInUIThread(IProgressMonitor monitor) {
			fReconciler.everythingHasChanged(0, fLimit); 
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		}
		
	}	
}
