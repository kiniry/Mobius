//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SimplifyProofTask.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package simplifyPlugin;

import jack.plugin.perspective.ICaseExplorer;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import java.io.File;
import java.io.InputStream;
import java.util.Date;

import jml2b.exceptions.InternalError;
import jpov.structure.Goal;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * ProofTask sending proofs to the Simplify prover.
 * @author A. Requet L. Burdy
 */
public class SimplifyProofTask extends ProofTask {
	private Simplify simplify;
	private String errors;
	private boolean[] results;
	public SimplifyProofTask() {
		super();
	}

	/**
	 * Creates a simplify proof task for proving the given jpo file.
	 * 
	 * @param jpo_file the jpo file that should be proved.
	 */
	public SimplifyProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	/**
	 * @param exp
	 */
	public SimplifyProofTask(ICaseExplorer exp) {
		
		super(exp);
	}

	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new SimplifyProofTask(jpo_file, c);
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
			startLoad();
			jpov = loadJpov();
//			if (jpov == null) {
//				// should always be true for Simplify, since the ProofTask is always
//				// created from an IFile
//				startLoad();
//				changed();
//				try {
//					jpov = JpovUtil.loadJpoFile(jpoFile);
//				} catch (LoadException e) {
//					setError(
//						"Error loading file",
//						"Exception catched: " + e.toString());
//					changed();
//					return;
//				} catch (IOException e) {
//					setError(
//						"Error loading file",
//						"Exception catched: " + e.toString());
//					changed();
//					return;
//				}
//				// the file object is not needed anymore
//				jpoFile = null;
//
//				numPos = jpov.getJmlFile().getNbPo();
//				changed();
//			}

			int nbPo = jpov.getJmlFile().getNbPo();
			results = new boolean[nbPo];
			// indicates that the proof starts
			startProof();
			changed();

			int lemme = 1;
			int index = 0;
			int file = 0;
			String readS = "";
			main_loop : while (!shouldStop && lemme <= nbPo) {

				try {
					File f =
						new File(
							jpov.getDirectory(),
							jpov.getName() + ".sim" + file++);
					if (!f.exists()) {
						setError(
							"Simplify output file have to be generated before proving.",
							f.getAbsolutePath());
						changed();
						return;
					}
					simplify =
						new Simplify(
							SimplifyPreferencePage.getSimplifyExe(),
							f.getAbsolutePath());
				} catch (SimplifyException e) {
					setError("Could not start simplify process", e.toString());
					changed();
					return;
				}

				readStream = new ReadStream(simplify);
				readStream.run();

				int tmpindexV, tmpindexI, tmpindexA;
				int currentLemma = 1;
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
							readS.indexOf(currentLemma + ": Valid.", index);
						tmpindexI =
							readS.indexOf(currentLemma + ": Invalid.", index);
						tmpindexA = readS.indexOf("Bad input:", index);
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
				InputStream es = simplify.getSimplify().getErrorStream();
				int len;
				byte[] ba = new byte[len = es.available()];
				if (len != 0) {
					es.read(ba, 0, len);
					addError(new String(ba));
					break main_loop;
				}
				// stops the simplify process
				simplify.stop();
			}

			// update the jpo file with the results.
			proveFile(jpov.getJmlFile());
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



	//@ requires goals != null;
	protected void proveGoals(String name, Goal[] goals, int cpt) {
		for (int i = 0; i < goals.length; i++) {
			Goal g = goals[i];
			g.setStatus("Simplify", new ProverSimplifyStatus(results[cpt++]));
		}
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
		return "Simplify";
	}


	public ProveAction factory() {
		return new ProveSimplifyAction();
	}

}
