//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;
import jack.util.Logger;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.Lemma;
import jpov.structure.Method;
import jpov.structure.Proofs;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyProofTask extends ProofTask {

	public HarveyProofTask() {
		super();
	}

	/**
	 * Creates a haRVey proof task for proving the given jpo file.
	 * @param jpo_file the jpo file that should be proved.
	 */
	public HarveyProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new HarveyProofTask(jpo_file, c);
	}

	public void run() {
		startLoad();
		changed();
		try {
			jpov = loadJpov();
		} catch (Exception e) {
			setError(
				"Error loading file",
				"Exception catched: " + e.toString());
			changed();
			return;
		}
		// the file object is not needed anymore
		jpoFile = null;

		try {
			updateFromJpov();
			changed();
			// indicates that the proof starts
			startProof();
			changed();
			Class[] ca = jpov.getJmlFile().getClasses();
			for (int i = 0; i < ca.length; i++)
				prove(
					jpov.getDirectory()
						+ File.separator
						+ ca[i].getName()
						+ ".rv"
						+ File.separator,
					ca[i]);
			endProof();
			changed();
		} finally {
			jpov = null;
			finished();
		}
	}

	/**
	 * @param class1
	 */
	private void prove(String name, Class c) {
		prove(name + "Invariant_well_definedness", c.getWellDefInvLemmas());
		prove(
			name + c.getName() + "_Static_Initialisation",
			c.getStaticInitLemmas());
		Method[] ma = c.getConstructors();
		for (int i = 0; i < ma.length; i++)
			prove(name, ma[i]);
		ma = c.getMethods();
		for (int i = 0; i < ma.length; i++)
			prove(name, ma[i]);
	}

	/**
	 * @param method
	 */
	private void prove(String name, Method method) {
		prove(name + method.getPmiName(), method.getLemmas());
	}

	/**
	 * @param proofs
	 */
	private void prove(String name, Proofs proofs) {
		Lemma[] la = proofs.getLemmas();
		for (int i = 0; i < la.length; i++)
			prove(name + "_" + i, la[i]);
	}

	/**
	 * @param lemma
	 */
	private void prove(String name, Lemma lemma) {
		Goal[] ga = lemma.getGoals();
		for (int i = 0; i < ga.length; i++) {
			if (!ga[i].isProved())
				prove(name + "_" + i, ga[i]);
		}
	}

	/**
	 * @param string
	 * @param goal
	 */
	private void prove(String string, Goal goal) {
		String[] cmds = { "/0/user/lburdy/Bin/Exe/haRVey.csh", string };
		try {
			Process p = Runtime.getRuntime().exec(cmds);
			InputStream s = p.getInputStream();
			int len;
			String output = "";
			do {
				byte[] ba = new byte[len = s.available()];
				if (len != 0) {
					s.read(ba, 0, len);
					output += new String(ba);
				} else if (isAlive(p)) {
					synchronized (s) {
						s.wait(100);
					}
				}
			} while (isAlive(p) || len != 0);
			increaseTried(1);
			if (output
				.indexOf("All proof obligations have been checked successfully.")
				!= -1) {
				goal.setStatus("Harvey", new HarveyProverStatus(true));
				increaseProved(1);
			} else
				goal.setStatus("Harvey", new HarveyProverStatus(false));
			changed();
		} catch (InterruptedException ie) {
			Logger.err.println("Exception " + ie.getMessage());
			return;
		} catch (IOException e) {
			Logger.get().println(
				"Error running haRVey on: " + string + ": " + e.toString());
		}
	}

	/**
	 * @param p
	 * @return
	 */
	private static boolean isAlive(Process p) {
		try {
			p.exitValue();
			return false;
		} catch (IllegalThreadStateException itse) {
			return true;
		}
	}

	public String getProverName() {
		return "Harvey";
	}

	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#proveGoals(java.lang.String, jpov.structure.Goal[], int)
	 */
	protected void proveGoals(String name, Goal[] goals, int cpt) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#factory()
	 */
	public ProveAction factory() {
		return new ProveHarveyAction();
	}

}
