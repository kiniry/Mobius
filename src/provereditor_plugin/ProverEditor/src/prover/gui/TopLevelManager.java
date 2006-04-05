package prover.gui;

import java.util.LinkedList;

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
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextViewer;
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
import prover.exec.IStreamListener;
import prover.exec.ITopLevel;
import prover.gui.editor.BasicPresentationReconciler;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.IColorConstants;
import prover.gui.editor.ProverEditor;
import prover.gui.jobs.AppendJob;
import prover.preference.PreferencePage;

public class TopLevelManager extends ViewPart implements IStreamListener, IColorConstants {
	private IDocument dc;	
	private LinkedList prooflist = new LinkedList();
	
	private ProverContext oldpc = ProverContext.empty;
	private ITopLevel top;
	private TextViewer tv;
	private ProverPresentation tp;
	private final static String GREETINGS = "This is ProverEditor version " + 
			ProverEditorPlugin.MAJORVERSION + "." + ProverEditorPlugin.VERSION + "." + ProverEditorPlugin.SUBVERSION +" !\n"; 
	
	AProverTranslator translator;
	private static TopLevelManager instance;
	
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
	
	public void createPartControl(Composite parent) {
		tv = new TextViewer(parent, SWT.V_SCROLL);
		tv.setEditable(false);
		
		if (dc == null) {
			dc = new Document("");
		}
		
		tv.setDocument(dc);
		tp = new ProverPresentation(tv);
//		tv.changeTextPresentation(tp, true);
		
		new AppendJob(tp, GREETINGS, VIOLET).prepare();
		
		//if (top == null) {
		//	respawn();
		//}
	}

	
	public void setFocus() {}
	
	
	private boolean bLock = false;

	private String msg;
	private BasicRuleScanner scanner;

	protected synchronized boolean lock() {
		if(bLock)
			return false;
		bLock = true; return true;
	}
	protected synchronized void unlock() {
		bLock = false;
	}
	public static IRegion findComment(AProverTranslator translator, FindReplaceDocumentAdapter fda, int start, boolean forward) throws BadLocationException {
		if(forward) return  findComment_forw(translator, fda, start);
		else return findComment_back(translator, fda, start);
	}
	
	private static IRegion findComment_forw(AProverTranslator translator, FindReplaceDocumentAdapter fda, int start) throws BadLocationException {
		IRegion r1 = fda.find(start, translator.getCommentBegin(), true, true, false, true);
		if(r1 == null)
			return null;
		IRegion r2 = fda.find(r1.getOffset() + 2, translator.getCommentEnd(), true, true, false, true);
		if(r2 == null)
			return null;
		return new Region(r1.getOffset(), (r2.getOffset() - r1.getOffset()) + 2);		
	}
	private static IRegion findComment_back(AProverTranslator translator, FindReplaceDocumentAdapter fda, int start) throws BadLocationException {
		IRegion r1 = fda.find(start, translator.getCommentEnd(), false, true, false, true);
		if(r1 == null)
			return null;
		IRegion r2 = fda.find(r1.getOffset(), translator.getCommentBegin(), false, true, false, true);
		if(r2 == null)
			return null;
		return new Region(r2.getOffset(), (r1.getOffset() - r2.getOffset()) + 2);		
	}
		
	protected synchronized boolean progress_intern (ProverContext pc) {
		if(isNewDoc(pc.doc))
			reset(pc);
		int oldlimit =pc.scan.getLimit();
		try {
			int ol = oldlimit;IRegion comment; IRegion r = null;
			do {
				r = pc.fda.find(ol, translator.getEndOfSentence(),true, true, false, true);
				
				comment = findComment(translator, pc.fda, ol, true);
				if(comment != null) {
					ol = comment.getOffset() + comment.getLength();
					//System.out.println(doc.get(r1.getOffset(), r1.getLength()));
				}
				else {
					if(r!= null){
						ol = r.getOffset() + r.getLength();
					}
				}
			} while(r != null && (isIn(comment, r.getOffset()) || 
					ol < r.getOffset())); 
	//				(r.getOffset() >= ol));

			//IRegion r = fda.find(oldlimit, "\\.[ \n\t]",true, true, false, true);
			if (r == null) {
				return false;
			}
			int newlimit = r.getOffset() + 1;
			try {
				String cmd = pc.doc.get(oldlimit, newlimit - oldlimit).trim();
				if(cmd.equals(""))
					return false;
				//append(cmd + "\n");
				top.clearBuffer();
				top.sendCommand(cmd);
				if(top.isAlive()) {
					msg = top.getBuffer();
					pc.scan.setLimit(newlimit);
				}
				else return false;
				
			} catch (AProverException e) {
				msg = e + top.getBuffer();
				return false;
			} 

			
		} catch (BadLocationException e) {return false;}		
		return true;
	}
	
	public void reset(ProverContext pc) {
		if(pc.doc != null) {
			oldpc = pc;
			reset();
		}
	}

	private boolean isNewDoc(IDocument doc) {
		return doc != oldpc.doc;
	}

	public String getMsg() {
		return msg;
	}
	
	private boolean isIn(IRegion region, int index) {
		return (region != null) && (region.getOffset() <= index) 
			&& (index < (region.getOffset() + region.getLength()));
	}
	protected synchronized boolean regress_intern(ProverContext pc) {
		if (isNewDoc(pc.doc)) {
			reset(pc);
			return false;
		}
		
		int oldlimit = pc.scan.getLimit();
		boolean proof = !top.isProofMode();
		if(oldlimit > 0)
			try {
				top.undo(1);
			} catch (AProverException e) {
				append(e.toString());
			}
		try {
			if(oldlimit > 0) {
				do {
					int ol = oldlimit;
					IRegion comment; 
					IRegion r = null;
					do {
						r = pc.fda.find(ol - 1, translator.getEndOfSentence(), false, true, false, true);
						comment = findComment(translator, pc.fda, ol, false);
						if(comment != null) {
							ol = comment.getOffset();
						}
						else {
							if(r!= null)
								ol = r.getOffset();
						}
					} while(r != null &&
							(isIn(comment, r.getOffset()) || 
							(ol  > r.getOffset())));
					String str = "";
					if (r != null) {
						try { 
							str = pc.doc.get(r.getOffset(), (oldlimit - 1) - r.getOffset());
						} catch (BadLocationException e) { 
							System.out.println(e + " : " + "I have gone bad bad bad!!!");
						}
					}
					if (r == null) {
						pc.scan.setLimit(0);
						UpdateJob uj = new UpdateJob(pc.sv.getPresentationReconciler(), oldlimit + 1);
						uj.schedule();
						return false;
					}
					pc.scan.setLimit(r.getOffset() + 1);
					UpdateJob uj = new UpdateJob(pc.sv.getPresentationReconciler(), oldlimit + 1);
					uj.schedule();
					oldlimit = r.getOffset() + 1;
					if(str.indexOf("Proof") != -1) {	
						proof = true;
					}
					if((prooflist.size() >0) &&(oldlimit <= ((Integer)prooflist.getLast()).intValue())) {
						prooflist.removeLast();
					}
				} while(proof &&(prooflist.size() %2 ==1));
			}
		} catch (BadLocationException e) {
				resetView();
				return false;
		}
		return true;
	}
	

	public boolean progress(ProverEditor ce, IDocument doc, FindReplaceDocumentAdapter fda, BasicSourceViewerConfig sv, BasicRuleScanner scan) {
		if(!lock())
			return true;
		int oldlimit =scan.getLimit();
		boolean b = progress_intern(new ProverContext(ce, doc, fda, sv, scan));
		UIJob job = new UpdateJob(sv.getPresentationReconciler(),scan.getLimit() +1);
		job.schedule();
		if(top.isProofMode()) {
			if(prooflist.size() % 2 == 0) 
				prooflist.add(new Integer(oldlimit));
		}
		else if(prooflist.size() % 2 == 1) 
				prooflist.add(new Integer(oldlimit));
		unlock();
		return b;
	}
	
	public boolean regress(ProverEditor ce, IDocument doc, FindReplaceDocumentAdapter fda, BasicSourceViewerConfig sv, BasicRuleScanner scan) {
		if(!lock())
			return true;
		boolean b = regress_intern(new ProverContext(ce, doc, fda, sv, scan));
		
		
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
						new AppendJob(tp, GREETINGS, VIOLET).prepare();
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
		
		//PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IFile path= (input instanceof IFileEditorInput) ? ((IFileEditorInput) input).getFile() : null;
	    translator = Prover.findProverFromFile(path.getRawLocation().toString()).getTranslator();
	    scanner = new BasicRuleScanner(translator.getProofRules());
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
			new AppendJob(tp, e.toString(), RED).prepare();
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
	
	private void forall_coloring(AppendJob job, StringBuffer src, int start, int gap) {
		int ind = start;
		//int len = src.length();
		while ((ind = src.indexOf("forall ", ind)) != -1) {
			// we have a forall
			job.addColor(gap + ind, 7, RED);
			// looking for the end....
			ind += 7;
			int i = src.indexOf(",", ind);
			if(i != -1) {
				job.addColor(gap + ind, (i - ind) + 1, DARKRED);
				ind = i;
			}
		}
	}
	private void hypname_coloring(AppendJob job, StringBuffer src, int start, int gap) {
		int ind = start;
		do {
			int end;
			if((src.indexOf("  ", ind) == ind) &&
					(src.indexOf(" ", ind + 2) == (end = src.indexOf(" :", ind)))) {
				job.addColor(ind + gap, (end - ind) + 2, GREEN);
			}
		} while ((ind = (src.indexOf("\n", ind) + 1)) != 0);
	}
	
	
	private void subgoals_coloring(AppendJob job, StringBuffer src, int start, int gap) {
		if((start = src.indexOf("subgoal 2", start)) != -1) {
			job.addColor(start + gap, (src.length() - 1) - start, GREY);
		}
	}

	public void append_subgoal(StringBuffer str, AppendJob job) {
		if (str.indexOf("Proof completed.") != -1) {
			job.add("\nProof Completed.\n", BLUE);
			return;
		}
		
		job.add("\n");
		
		int goalindex;
		String separator = "-----------------------------------------------------------------------------------";
		if((goalindex = str.indexOf(separator)) == -1) {
			return;
		}
		StringBuffer hypos = new StringBuffer(str.substring(0, goalindex - 2));
		StringBuffer goals = new StringBuffer(str.substring(goalindex + separator.length()));
		int gap = job.getLength();
		job.add(hypos);
		forall_coloring(job, hypos, 0, gap);
		hypname_coloring(job, hypos, 0, gap);
		job.add(separator);
		gap = job.getLength();
		
		job.add(goals);
		forall_coloring(job, goals, 0, gap);
		subgoals_coloring(job, goals, 0, gap);

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
		
		
		// Error handling
		String [] errorExpressions = translator.getErrorExpressions();
		
		for (int i = 0; (i < errorExpressions.length) && (ind == -1); i++){
			ind = str.indexOf(errorExpressions[i]);
		}
//		if(ind != -1) {
//			String hyps = str.substring(0, ind);
//			if (hyps.indexOf(" subgoal") != -1) {
//				append_subgoal(new StringBuffer(hyps), job);
//				job.add("\n\n");
//			}
//			
//			String err = str.substring(ind);
//			int gap = job.getLength();
//			job.add(err);
//			job.addColor(gap, str.length()- ind -1, RED);
//			job.add("\n");
//		}
//		else if (str.indexOf(" subgoal") != -1) {
//			append_subgoal(new StringBuffer(str), job);
//			job.add("\n\n");
//		}
//		else if (str.indexOf("Proof completed.") != -1) {
//			job.add("\nProof Completed.\n", BLUE);
//		}
//		else {
		job.add(str);
		//System.out.println(str);
//		}
		
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
