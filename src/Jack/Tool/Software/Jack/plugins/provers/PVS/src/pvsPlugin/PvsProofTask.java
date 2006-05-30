//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SimplifyProofTask.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package pvsPlugin;

import jack.plugin.JpovUtil;
import jack.plugin.edit.EditedFile;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.Date;
import java.util.Vector;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LoadException;
import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.Method;
import jpov.structure.Proofs;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * ProofTask sending proofs to the Simplify prover.
 * @author A. Requet L. Burdy
 */
public class PvsProofTask extends ProofTask {
	private PvsRunner pvs;
	private String errors;

	public PvsProofTask() {
		super();
	}

	/**
	 * Creates a simplify proof task for proving the given jpo file.
	 * 
	 * @param jpo_file the jpo file that should be proved.
	 */
	public PvsProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new PvsProofTask(jpo_file, c);
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
		numToTry = getNumPos();
	}

	/**
	 * Tries to prove the current jpo file using the Simplify 
	 * prover.
	 */
	public void run() {
		ReadStream readStream = null;
		try {
			if (jpov == null) {
				// should always be true for Simplify, since the ProofTask is always
				// created from an IFile
				startLoad();
				changed();
				try {
					jpov = JpovUtil.loadJpoFile(new EditedFile(jpoFile));
				} catch (LoadException e) {
					setError(
						"Error loading file",
						"Exception catched: " + e.toString());
					changed();
					return;
				} catch (IOException e) {
					setError(
						"Error loading file",
						"Exception catched: " + e.toString());
					changed();
					return;
				}
				// the file object is not needed anymore
				jpoFile = null;

				numPos = jpov.getJmlFile().getNbPo();
				changed();
			}

			int nbPo = jpov.getJmlFile().getNbPo();
			boolean[] results = new boolean[nbPo];
			// indicates that the proof starts

			int lemme = 1;
			int index = 0;
			String readS = "";

			try {
				File f = File.createTempFile("jackPvs", ".el");
				BufferedOutputStream ostream =
					new BufferedOutputStream(new FileOutputStream(f));
				PrintStream stream = new PrintStream(ostream);
				stream.println(
					"(change-context \"" + jpov.getDirectory() + "\")");
				stream.println("(typecheck \"" + jpov.getName() + "\")");
				//				stream.println(
				//					"(prove-tccs-pvs-file \"" + jpov.getName() + "\")");
				stream.println("(save-context)");
				stream.close();
				ostream.close();
				String[] cmds =
					{
						PvsPlugin.getPvsExe(),
						"-batch",
						"-q",
						"-l",
						f.getAbsolutePath()};
				Process p = Runtime.getRuntime().exec(cmds);
				synchronized (this) {
					wait(1000);
					while (PvsRunner.isAlive(p))
						wait(1000);
				}
				startProof();
				changed();
				f = File.createTempFile("jackPvs", ".el");
				ostream = new BufferedOutputStream(new FileOutputStream(f));
				stream = new PrintStream(ostream);
				stream.println(
					"(change-context \"" + jpov.getDirectory() + "\")");
				stream.println(
					"(prove-formulas-pvs-file \"" + jpov.getName() + "\")");
				stream.println("(save-context)");
				stream.close();
				ostream.close();
				pvs = new PvsRunner(PvsPlugin.getPvsExe(), f.getAbsolutePath());
			} catch (PvsException e) {
				setError("Could not start simplify process", e.toString());
				changed();
				return;
			}

			readStream = new ReadStream(pvs);
			readStream.run();

			int tmpindexV, tmpindexI, tmpindexA;
			int currentLemma = 0;
			index = 0;
			readS = "";
			while (!shouldStop && readStream.isAliv()) {
				String str;
				do {
					str = readStream.read(null);
				} while (!shouldStop && str == null && readStream.isAliv());
				readS = readS.substring(index, readS.length());
				readS = readS + str;
				index = 0;
				while (!shouldStop) {
					tmpindexV =
						readS.indexOf("t" + currentLemma + " proved", index);
					tmpindexI =
						readS.indexOf("t" + currentLemma + " unproved", index);
					tmpindexA =
						readS.indexOf(
							"T" + currentLemma + " has an existing",
							index);
					if (tmpindexV != -1
						&& (tmpindexI == -1 || tmpindexI > tmpindexV)
						&& (tmpindexA == -1 || tmpindexA > tmpindexV)) {
						increaseTried(1);
						increaseProved(1);
						changed();
						results[lemme - 1] = true;
						lemme++;
						currentLemma++;
						index = tmpindexV + 1;
					} else if (
						tmpindexI != -1
							&& (tmpindexA == -1 || tmpindexA > tmpindexI)) {
						increaseTried(1);
						changed();
						results[lemme - 1] = false;
						lemme++;
						currentLemma++;
						index = tmpindexI + 1;
					} else if (tmpindexA != -1) {
						increaseTried(1);
						changed();
						lemme++;
						currentLemma++;
						addError(readS.substring(index, readS.length()));
						index = tmpindexA + 1;
					} else
						break;
				}

			}
			readStream.stopped();
			// stops the simplify process
			pvs.stop();

			// update the jpo file with the results.
			proveFile(jpov.getJmlFile(), results, 0);
			if (errors != null) {
				endProof();
				setError("Errors occured during the proof: ", errors);
				changed();
			} else {
				// indicates that the proof ended normally
				endProof();
				changed();
				if (shouldStop) {
					addError(readS + "\nlemme: " + lemme + "\nindex: " + index);
					setError("Proof task has been stopped before end ", errors);
					changed();
				}
			}
		} catch (Exception e) {
			throw new InternalError(e.getMessage());
		} finally {
			if (readStream != null)
				readStream.stopped();
			jpov = null;
			finished();
		}
	}

	/**
	 * Tries to prove each of the lemmas within the file.
	 */
	//@ requires simplify != null;
	//@ requires file != null;
	private void proveFile(JmlFile file, boolean[] results, int cpt) {
		Class[] classes = file.getClasses();
		for (int i = classes.length - 1; i >= 0; i--) {
			cpt = proveClass(classes[i], results, cpt);
		}
		file.updateStatus();
	}

	/**
	 * Tries to prove each of the lemmas associated to the class.
	 */
	//@ requires simplify != null;
	//@ requires c != null;
	private int proveClass(Class c, boolean[] results, int cpt) {
		cpt = proveMethods(c.getMethods(), results, cpt);
		cpt = proveMethods(c.getConstructors(), results, cpt);
		cpt = proveProofs(c.getStaticInitLemmas(), results, cpt);
		return proveProofs(c.getWellDefInvLemmas(), results, cpt);

	}

	//@ requires simplify != null;
	//@ requires methods != null;
	private int proveMethods(Method[] methods, boolean[] results, int cpt) {
		for (int i = 0; i < methods.length; ++i) {
			Method m = methods[i];
			cpt = proveProofs(m.getLemmas(), results, cpt);
			cpt = proveProofs(m.getWellDefinednessLemmas(), results, cpt);
			m.updateStatus();
		}
		return cpt;
	}

	/**
	 * Tries to prove the given proof.
	 */
	//@ requires simplify != null;
	//@ requires p != null;
	private int proveProofs(Proofs p, boolean[] results, int cpt) {
		// the LemmaViewer array correspond to a list of cases
		Lemma[] lemmas = p.getLemmas();
		for (int i = 0; i < lemmas.length; ++i) {
			Lemma lemma = lemmas[i];
			cpt = proveGoals(lemma.getGoals(), results, cpt);

		}
		return cpt;
	}

	//@ requires goals != null;
	private int proveGoals(Goal[] goals, boolean[] results, int cpt) {
		for (int i = 0; i < goals.length; i++) {
			Goal g = goals[i];
			g.setStatus("PVS", new PvsProverStatus(results[cpt++]));
		}
		return cpt;
	}

	private void addError(String description) {
		// append the error to the list of errors
		if (errors == null) {
			errors = description;
		} else {
			errors += "\n" + description;
		}

	}

	public String getProverName() {
		return "PVS";
	}

	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#proveGoals(java.lang.String, jpov.structure.Goal[], int)
	 */
	protected void proveGoals(String name, Goal[] goals, int cpt) {
		// TODO Auto-generated method stub
		
	}

	public ProveAction factory() {
		return new PvsProveAction();
	}
	
//	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
//		return new PvsProofTask(jpo_file, c);
//	}

}

class ReadStream extends Thread {

	PvsRunner simp;
	InputStream s;
	Vector readed;
	boolean continu;

	synchronized String read(byte[] ba) {
		if (ba == null) {
			if (!readed.isEmpty()) {
				return (String) readed.remove(0);
			}
		} else {
			readed.add(new String(ba));
		}
		return null;
	}

	ReadStream(PvsRunner s) {
		simp = s;
		this.s = s.getPvs().getInputStream();
		continu = true;
		readed = new Vector();
	}

	void stopped() {
		continu = false;
	}

	boolean isAliv() {
		return continu || !readed.isEmpty();
	}

	public void run() {
		try {

			int len;
			byte[] ba;
			do {
				ba = new byte[len = s.available()];
				if (len != 0) {
					s.read(ba, 0, len);
					read(ba);
				} else {
					synchronized (s) {
						s.wait(100);
					}
				}
			} while (PvsRunner.isAlive(simp.getPvs()) && continu);
			//Encore une lecture
			do {
				ba = new byte[len = s.available()];
				if (len != 0) {
					s.read(ba, 0, len);
					read(ba);
				}
			} while (len != 0);
			stopped();
		} catch (InterruptedException ie) {
			throw new InternalError("Exception " + ie.getMessage());
		} catch (IOException ioe) {
			throw new InternalError("Exception " + ioe.getMessage());
		}
	}


}