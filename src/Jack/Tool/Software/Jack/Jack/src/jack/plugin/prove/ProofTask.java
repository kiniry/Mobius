//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: ProofTask.java
 /*
 /********************************************************************************
 /* Warnings/Remarks:
 /*******************************************************************************/
package jack.plugin.prove;

import jack.plugin.JackPlugin;
import jack.plugin.JpovUtil;
import jack.plugin.compile.PoGenerator;
import jack.plugin.edit.EditAction;
import jack.plugin.edit.EditedFile;
import jack.plugin.perspective.ICaseExplorer;
import jack.util.Logger;

import java.io.IOException;
import java.util.Date;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import jml2b.exceptions.LoadException;
import jpov.JpoFile;
import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.Method;
import jpov.structure.Proofs;
import jpov.viewer.tree.TreeItemSelection;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

/**
 * Class corresponding to a proof task that must be (or is) performed.
 * 
 * @author A. Requet, L. Burdy
 */
public abstract class ProofTask extends Thread {
	/**
	 * The state the task is currently in. Can be one of:
	 * <ul>
	 * <li><code>WAITING</code>,
	 * <li><code>STARTING</code>,
	 * <li><code>LOADING</code>,
	 * <li><code>RUNNING</code>,
	 * <li><code>FINISHED</code> or
	 * <li><code>ERROR</code>
	 * </ul>
	 */
	protected int currentState;

	/**
	 * The <code>.jpo</code> file that should be used. It can be null if the
	 * prooftask was already created with a <code>Jpov</code> object.
	 * Otherwise, it is used to load the <code>Jpov</code> object.
	 */
	protected IFile jpoFile;

	/**
	 * The name of the compilation unit that is proved.
	 */
	private String fileName;

	/**
	 * The <code>Jpov</code> element corresponding to this proof task.
	 */
	protected JpoFile jpov;

	/* @ invariant jpov == null ==> jpoFile != null; */

	/**
	 * Start date of the task. This is the date when the proof began, after the
	 * jpov file has been loaded.
	 */
	protected Date startDate;

	/**
	 * End date of the task.
	 */
	private Date endDate;

	/**
	 * Creation date of the task.
	 */
	private Date creationDate;

	/**
	 * The proof list this task belongs to.
	 */
	private ProofTaskList proofList;

	/* @ invariant endDate != null ==> startDate != null; */

	/**
	 * Total number of proof obligations.
	 */
	protected int numPos = -1;

	/**
	 * Number of proved proof obligations.
	 */
	protected int numProved;

	/**
	 * Total number of proof obligations that must be tried.
	 */
	protected int numToTry;

	/**
	 * Number of proof obligations that have been tried.
	 */
	private int numTried;

	//@ invariant numTried <= numToTry;

	/**
	 * Boolean variable indicating that the thread should stop. Subclasses are
	 * exepected to check it regularly and to stop if this variable is set to
	 * true.
	 */
	protected boolean shouldStop;

	/**
	 * String containing the error description in case where an error occured.
	 */
	private String errorDescription;

	/**
	 * String containing error details in case where an error occured and
	 * details are availables.
	 */
	private String errorDetails;

	private ICompilationUnit ci;

//	protected IJavaProject javaProject;

	/**
	 * Returns true iff proofs are currently performed on this task.
	 */
	public boolean isRunning() {
		return currentState == RUNNING;
	}

	public ProofTask() {
	}

	public abstract ProofTask factory(IFile jpoFile, ICompilationUnit cu);
	public abstract ProveAction factory();
	/**
	 * Returns the state of the task. The returned state can be one of:
	 * <ul>
	 * <li><code>RUNNING</code>,
	 * <li><code>FINISHED</code>,
	 * <li><code>LOADING</code>,
	 * <li><code>WAITING</code> or
	 * <li><code>ERROR</code>
	 * </ul>
	 */
	public int getCurrentState() {
		return currentState;
	}

	public String getStringState() {
		switch (currentState) {
			case RUNNING :
				return "Running";
			case FINISHED :
				return "Finished";
			case WAITING :
				return "Waiting";
			case ERROR :
				return "Error";
			case STOPPED :
				return "Stopped";
			default :
				return "Unknown";
		}
	}

	public String getFileName() {
		return fileName;
	}

	/**
	 * Function that asks the thread to stop when he can.
	 */
	public synchronized void stopAsSoonAsYouCanPlease() {
		shouldStop = true;
		currentState = STOPPED;
	}

	/**
	 * Returns the number of proof obligations that have already been tried.
	 * 
	 * @return the number of proof obligations already tried.
	 */
	public int getPoTried() {
		return numTried;
	}

	/**
	 * Returns the number of proof obligations that still have to be tried.
	 * 
	 * @return the number of proof obligations that still have to be tried.
	 */
	public int getNumToTry() {
		return numToTry;
	}

	/**
	 * Returns the number of proved proof obligations.
	 * 
	 * @return the number of proved proof obligations.
	 */
	public int getPoProved() {
		return numProved;
	}

	/**
	 * Return the creation date of the task.
	 * 
	 * @return the creation date of the task.
	 */
	public Date getCreationDate() {
		return creationDate;
	}

	/**
	 * Return the start date of teh task. That is the time where the proof
	 * started.
	 * 
	 * @return the start date of the task.
	 */
	public Date getStartDate() {
		return startDate;
	}

	/**
	 * Returns the end date of the task.
	 * 
	 * @return the end date fo the task.
	 */
	public Date getEndDate() {
		return endDate;
	}

	/**
	 * Returns the total number of proof obligations.
	 * 
	 * @return the total number of proof obligations.
	 */
	public int nbPo() {
		return numPos;
	}

	/**
	 * Notify the viewers that the value has changed. This method should be
	 * called by subclasses in order to ensure that the displayed values are up
	 * to date.
	 */
	protected void changed() {
		proofList.taskChanged(this);
	}

	/**
	 * Notify that the proof has finished. This method should be called by
	 * subclasses when they have finished their work.
	 */
	protected void finished() {
		proofList.taskFinished(this);
	}

	/**
	 * Indicates that the proof started. This method should be called by
	 * subclasses when the proof starts.
	 */
	protected void startProof() {
		// creates the starting date
		startDate = new Date();
		// updates the state of the object
		currentState = RUNNING;
		updateToTry();
		this.changed();
	}

	/**
	 * Indicates that the proof has ended. This method should be called by
	 * subclasses when they have ended their proof tasks normally.
	 * 
	 * Note that <code>finished</code> must also be called at the end of the
	 * task.
	 */
	protected void endProof() {
		endDate = new Date();
		currentState = FINISHED;
		updateFromJpov();
		try {
			jpov.save();
		} catch (IOException ex) {
			String str = ex.toString();
			Logger.err.println(str);
			setError("I/O Error", str);
		}
		this.changed();
		if(ehl != null) {
			Iterator i = ehl.getSelectedGoals().iterator();
			while(i.hasNext()) {
				((Goal)i.next()).setUnselected();
			}
			ehl.resetSelectedGoals();
		}
		// now we shall update view (...if we can...)
		UIJob job = new CaseViewerUpdateJob(ce);
		job.schedule();
	}

	/**
	 * Indicates that the ProofTask started loading the jpo file. This method
	 * should be called by subclasses when they load the jpo file.
	 */
	protected void startLoad() {
		currentState = LOADING;
		this.changed();
	}

	/**
	 * Indicates that an error occured.
	 * 
	 * @param description
	 *            a short (one line) description of the error.
	 * @param details
	 *            a more detailed description of the error, if available.
	 */
	protected void setError(String description, String details) {
		errorDescription = description;
		errorDetails = details;
		currentState = ERROR;
		this.changed();
	}

	/**
	 * Increase the number of tried proof obligations of <code>delta</code>.
	 * Should be called regularly by subclasses.
	 */
	protected void increaseTried(int delta) {
		numTried += delta;
		this.changed();
	}

	/**
	 * Increase the number of proved proof obligations of <code>delta</code>.
	 * Should be called regularly by subclasses.
	 */
	protected void increaseProved(int delta) {
		numProved += delta;
	}

	/**
	 * Returns the description of the last error encountered.
	 * <p>
	 * This method will only provide meaningfull values if the current state is
	 * <code>ERROR</code>.
	 * 
	 * @return the description of the last error encountered, if any.
	 */
	//@ requires currentState == ERROR;
	public String getErrorDescription() {
		return errorDescription;
	}

	/**
	 * Returns detail about the last error encountered.
	 * <p>
	 * In case were no details are available, returns <code>null</code>.
	 * 
	 * @return detailed information on the last error encountered,
	 *         <code>null</code> in case where no information is available.
	 */
	public String getErrorDetails() {
		return errorDetails;
	}

	/**
	 * Starts the proof.
	 */
	public abstract void run() ;
	/**
	 * Updates the status from the content of the Jpov. Should be called when
	 * the jpov file changes. This method is typically called after the jpov
	 * file is loaded.
	 */
	protected void updateFromJpov() {
		numPos = jpov.getJmlFile().getNbPo();
		numProved = jpov.getJmlFile().getNbPoProved();
	}

	/**
	 * Updates the <code>numToTry</code> variable depending on the
	 * <code>numPos</code> and <code>numProved</code> variables.
	 */
	private void updateToTry() {
		numToTry = numPos - numProved;

	}

	/**
	 * Creates a new ProofTask for proving the specified jpo file.
	 */
	/*
	 * @ @ requires jpov != null; @
	 */
	protected ProofTask(JpoFile jpov) {
		super("ProofTask");
		this.jpov = jpov;
		currentState = WAITING;
		creationDate = new Date();
		// initialize number of proof obligations and proved proof
		// obligations

		fileName = jpov.getJmlFile().getFileName().getName();
		updateFromJpov();
		numTried = numProved;
		
	}

	/**
	 * Creates a new ProofTask for Proving the specified jpo file.
	 */
	/*
	 * @ @ requires jpo_file != null; @
	 */
	protected ProofTask(IFile jpo_file, ICompilationUnit c) {
		super("ProofTask");
//		javaProject = c.getJavaProject();
		jpoFile = jpo_file;
		currentState = WAITING;
		creationDate = new Date();
		fileName = JpovUtil.getJpoPrefix(new EditedFile(jpo_file)) + ".java";
		
		//fileName = jpov.getJmlFile().getFileName().getName();
		numToTry = -1;
		ci = c;
	}
	
	/**
	 * @param c
	 */
	public ProofTask(ICaseExplorer c) {
		Logger.get().println(c.getTreeSelection());
	}

	/**
	 * load the jpov file which we were told about in the constructor.
	 * It also initializes the variable jpov and numPos.
	 * @return  the jpov file loaded
	 */
	protected JpoFile loadJpov(){
		// should always be true for Simplify, since the ProofTask is always
		// created from an IFile
		JpoFile jpov;
		if(this.jpov != null)
			return this.jpov;
		else {
			try {
				jpov = JpovUtil.loadJpoFile(new EditedFile(jpoFile));
			} catch (LoadException e) {
				setError(
						"Error loading file",
						"Exception catched: " + e.toString());
				changed();
				return null;
			} catch (IOException e) {
				setError(
						"Error loading file",
						"Exception catched: " + e.toString());
				changed();
				return null;
			}
			// the file object is not needed anymore
			jpoFile = null;
			this.jpov = jpov;
			numPos = jpov.getJmlFile().getNbPo();
			Class[] c = jpov.getJmlFile().getClasses();
			for (int i = 0; i < c.length; i++) c[i].selectAll();
		}
		fileName = jpov.getJmlFile().getFileName().getName();
		return jpov;
	}
	
	
	/**
	 * Sets the ProofTaskList this task belongs to.
	 */
	void setProofTaskList(ProofTaskList list) {
		proofList = list;
	}

	public synchronized void start() {
		currentState = STARTING;
		super.start();
	}

	void recompile() {
		PoGenerator.compile(ci);
	}

	void edit() {
		EditAction.edit(ci);
	}

	void reprove(ProofTask pt) {

		IViewPart view;
		Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow()
				.getShell();

		try {
			// Warning: showing the page modifies the selection.
			// So, the selection must be stored before calling page.showView
			view = PlatformUI.getWorkbench().getActiveWorkbenchWindow()
					.getActivePage().showView(JackPlugin.JACK_PROOF_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(shell, JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		ProofView proof_view = (ProofView) view;

		List errors = null;
		if (JackPlugin.isLock(ci.getResource())) {
			return;
		}
		IFile java_file = (IFile) ci.getResource();
		IFile jpo_file = JackPlugin.getJpoFile(ci);

		if (jpo_file != null) {
			JackPlugin.lock(ci.getResource());
			proof_view.addProof(pt.factory(jpo_file, ci));
		} else {
			if (errors == null) {
				// creates the error vector if needed
				errors = new Vector();
			}
			// adds the file name
			errors.add(java_file.getName());
		}
		if (errors != null) {
			// errors have been encountered
			String message = "The following should be compiled before trying to prove them:";
			// adds the list of files
			Iterator files = errors.iterator();
			while (files.hasNext()) {
				message += "\n" + (String) files.next();
			}

			MessageDialog.openInformation(shell, JackPlugin.DIALOG_TITLE,
				message);
		}
	}
	
	/**
	 * Tries to prove each of the lemmas within the file by calling the proveGoals method.
	 * @param The jmlfile in which the lemmas are.
	 */
	//@ requires simplify != null;
	//@ requires file != null;
	protected void proveFile(JmlFile file) {
		Class[] classes = file.getClasses();
		int cpt = 0;
		for (int i = classes.length - 1; !shouldStop && i >= 0; i--) {
			cpt = proveClass(classes[i], cpt);
		}
		file.updateStatus();
	}
	/**
	 * Tries to prove each of the lemmas associated to the class.
	 */

	private int proveClass(Class c, int cpt) {
		cpt = proveMethods(c.getMethods(), cpt);
		if (shouldStop) return cpt;
		cpt = proveMethods(c.getConstructors(), cpt);
		if (shouldStop) return cpt;
		cpt = proveProofs("StaticInitLemmas", c.getStaticInitLemmas(), cpt);
		if (shouldStop) return cpt;
		return proveProofs("WellDefinedLemmas", c.getWellDefInvLemmas(), cpt);

	}

	private int proveMethods(
		Method[] methods,
		int cpt) {
		for (int i = 0; i < methods.length; ++i) {
			Method m = methods[i];
			cpt = proveProofs(m.getName(), m.getLemmas(), cpt);
			cpt = proveProofs(m.getName(), m.getWellDefinednessLemmas(), cpt);
			m.updateStatus();
		}
		return cpt;
	}

	/**
	 * Tries to prove the given proof.
	 * @param method
	 */
	//@ requires simplify != null;
	//@ requires p != null;
	private int proveProofs(String method, Proofs p, int cpt) {
		// the LemmaViewer array correspond to a list of cases
		Lemma[] lemmas = p.getLemmas();
		for (int i = 0;  i < lemmas.length; ++i) {
			Lemma lemma = lemmas[i];
			Goal[] goals = lemma.getGoals();
			if (!shouldStop) {
				int count = 0;
				for(int j = 0; j < goals.length; j++) {
					if (goals[j].isSelected()) count ++;
				}
				Goal [] g = new Goal[count];
				count = 0;
				for(int j = 0; j < goals.length; j++) {
					if (goals[j].isSelected()){
						g[count] = goals[j];
						count++;
					}
				}
				proveGoals(method + "_" + (i + 1), g, cpt);
			}
			cpt += goals.length;

		}
		return cpt;
	}
	
	/**
	 * Prover and update the status for the given goals.
	 * @param name The name of the goal 
	 * @param goals the list of goals to prove
	 * @param cpt The goal number
	 */
	protected abstract void proveGoals(String name, Goal[] goals, int cpt);
	
	
	void unlock() {
		if (ci != null)
			JackPlugin.unLock(ci.getResource());
	}

	/**
	 * return the name of the prover used by this ProofTask.
	 */
	public abstract String getProverName();

	/**
	 * Constant corresponding to the state. That is when the proof has either
	 * terminited normally, or been aborted.
	 */
	public static final int FINISHED = 1;
	/**
	 * Constant corresponding to the waiting state. That is, when the task has
	 * not been started yet, and is waiting that another task finishes for
	 * starting.
	 */
	public static final int WAITING = 2;
	/**
	 * Constant corresponding to the running state. That is, when the proof is
	 * currently running.
	 */
	public static final int RUNNING = 3;
	/**
	 * Constant corresponding to the loading state. That is, when the task is
	 * loading the list of proof obligations.
	 */
	public static final int LOADING = 4;

	/**
	 * Constant corresponding to the starting state. That is, when the task has
	 * been selected for run but has not begin running yet.
	 */
	public static final int STARTING = 5;

	public static final int STOPPED = 6;
	/**
	 * Constant corresponding to the error state. That is, when the task has
	 * stopped due to an error.
	 */
	public static final int ERROR = 7;

	private TreeItemSelection ehl;

	private ICaseExplorer ce;
	/**
	 * @return
	 */
	public int getNumPos() {
		return numPos;
	}

	/**
	 * @param jpoFile2
	 */
	public void setJPov(JpoFile jpoFile2) {
		jpov =jpoFile2;
		
	}

	/**
	 * @param ehl
	 */
	public void setEndOp(TreeItemSelection ehl) {
		this.ehl = ehl;
		
	}
	/**
	 * @param ehl
	 */
	public void setExplorer(ICaseExplorer exp) {
		this.ce = exp;
		
	}
	
	/**
	 * This method is called when the partial mode is called.
	 * @param win
	 *
	 */
	public void setPartial(String repos) {
		
	}

}