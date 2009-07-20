//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: AProofTask.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package coqPlugin.prooftask;

import jack.plugin.perspective.ICaseExplorer;
import jack.plugin.prove.ProofTask;
import jack.util.Logger;

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import jml2b.exceptions.LanguageException;
import jml2b.pog.lemma.GoalStatus;
import jpov.JpoFile;
import jpov.structure.Goal;
import jpov.structure.Lemma;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import prover.exec.AProverException;
import prover.exec.toplevel.exceptions.ToplevelException;
import prover.plugins.exceptions.ProverException;
import coqPlugin.CoqInteractive;
import coqPlugin.CoqLanguage;
import coqPlugin.CoqTranslationResult;
import coqPlugin.ProverCoqStatus;
import fr.inria.everest.coq.sugar.CoqTop;
import fr.inria.everest.coq.sugar.CoqUtils;

/**
 * ProofTask sending proofs to the Coq prover.
 * @author J. Charles
 */
public abstract class AProofTask extends ProofTask {
	private CoqTop coq;
	private String errors;
	private boolean bMustProveAll = false;
	private String [][] myTactics = null;
	private boolean bUnrecoverableState = false;
	private String libFile;
	private String fLibName;
	private File dir;
	
	/**
	 * The simple constructor
	 */
	public AProofTask() {
		super();
	}
	

	/**
	 * Creates a coq proof task for proving the given jpo file.
	 * @param jpo_file the jpo file that should be proved.
	 * @param c The CompilationUnit context.
	 */
	public AProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	
	/**
	 * @param c
	 */
	public AProofTask(ICaseExplorer c) {
		
		super(c);
	}


	/**
	 * Creates a new ProofTask object of the right class.
	 * @param jpo_file the jpo file that should be proved.
	 * @param c The CompilationUnit context.
	 */
	public abstract ProofTask factory(IFile jpo_file, ICompilationUnit c);


	/**
	 * Tries to prove the current jpo file using the Coq prover.
	 */
	public void run() {
		myTactics = getTactics();
		startLoad();
		JpoFile jpov = loadJpov();
		bUnrecoverableState = false;
		if (jpov == null) { // an error state
			return;
		}
		
		libFile = new File(dir = jpov.getDirectory(),jpov.getName()).toString() + ".v";
		bMustProveAll = getCoqMustProveAll();

		try {
			coq = CoqUtils.createNewCoqTop();
			coq.restart();
		} catch (AProverException e) {
			setError("Could not start Coq process", e.toString());
			changed();
			return;
		}
		
		
		// indicates that the proof starts
		startProof();

		try {
			coq.sendCommand("Require Import Bool.");
			coq.sendCommand("Require Import ZArith.");
			coq.sendCommand("Require Import Classical.");
			coq.sendCommand("Add LoadPath \"" + libFile.substring(0, libFile.lastIndexOf(File.separator)) + "\".");
			String name = libFile.substring(libFile.lastIndexOf(File.separator) + 1);
			name = name.substring(0, name.length() - 2);
			fLibName = name;
//			coq.sendCommand("Require Import \"" + name + "_classes\".");
			
//			coq.sendCommand("Load \"user_extensions.v\".");

			coq.sendCommand("Require Import \"" + name + "\".");
			coq.sendCommand("Import JackLogic.");
			
			coq.sendCommand("Open Scope Z_scope.");
			coq.sendCommand("Open Scope J_Scope.\n");
			

		} catch (AProverException e1) {
			setError("There was a problem with the coq output...", e1.toString());
			return;
		}
		// start to prove the jpo file.
		proveFile(jpov.getJmlFile());
		
		// ends the proof
		endProof();
		coq.stop();
		finished();
	}
	
	
	/**
	 * Say wether or not we should prove already proven lemmas
	 * @return true if everything must be proven
	 */
	public abstract boolean getCoqMustProveAll();


	/**
	 * Tries to prove the given goals which have all the same hypothesis.
	 * @param name A string representing the path of the goals in the class
	 * @param goals The goals to prove.
	 * @param cpt The number of the already tried goals.
	 */
	protected void proveGoals(String name, Goal[] goals, int cpt) {
		if (goals.length == 0)
			return;
		Lemma l = (Lemma) goals[0].getParent();
		try {
			coq.startSection("JackProof");
			CoqLanguage.resetNames();
			List list = CoqInteractive.getLemmasHypothesisList(l);
			Iterator iter = list.iterator();
			while (!bUnrecoverableState && iter.hasNext()) {
				try {
					coq.sendCommand((String)iter.next());
				} catch (ToplevelException e) {
					// We terminate the proof
					bUnrecoverableState = true;
				}
			}
			for (int i = 0; i < goals.length; i++) {
				
				Goal g = goals[i];
				GoalStatus gs = g.getState();
				if((bMustProveAll || !gs.isProved()) && !bUnrecoverableState) {
					boolean res = false;
					try {
		
						res = proveLemma(name + "_" +(i +1), g);
						if (res) increaseProved(1);

					} catch (ToplevelException e) {
						/*
						 * Let me say something sad: as coq seems not stable 
						 * enough when we catch such an exception all we can
						 * do is but terminate and restart it.
						 */
						// We terminate the proof
						Logger.err.print(name + "_" + (i +1) + " >> ");
						Logger.err.println(e);
						Logger.get().print("Reanimating Coq...");
						try {
							coq.stop();
						}
						catch(Exception en) {
							
						}
						coq = CoqUtils.createNewCoqTop();
						coq.restart();
						coq.sendCommand("Require Import Bool.");
						coq.sendCommand("Require Import ZArith.");
						coq.sendCommand("Require Import Classical.");
						coq.sendCommand("Add LoadPath \"" + libFile.substring(0, libFile.lastIndexOf(File.separator)) + "\".");
//						coq.sendCommand("Require Import \"" + fLibName + "_classes\".");						
//						coq.sendCommand("Load \"user_extensions.v\".");
						coq.sendCommand("Require Import \"" + fLibName + "\".");
					
						coq.sendCommand("Import JackLogic.");
						coq.sendCommand("Open Scope Z_scope.");
						coq.sendCommand("Open Scope J_Scope.");
						coq.startSection("JackProof");
						iter = list.iterator();
						while (!bUnrecoverableState && iter.hasNext()) {
							try {
								coq.sendCommand((String)iter.next());
							} catch (ToplevelException e1) {
								// We terminate the proof
								bUnrecoverableState = true;
							}
						}
						Logger.get().println("done.");
						res = false;
						//bUnrecoverableState = true;
					}
					catch (ProverException e) {
						addError("Lemma " + cpt +":\n" + e.toString());
					}
					if (res)
						g.setStatus("Coq", new ProverCoqStatus(res));
					increaseTried(1);
					cpt ++;
				}
			}
		} catch (Exception e) {
			addError("Hypothesis " + cpt +":\n" + e.toString());
			Logger.err.println("Hypothesis " + cpt +":\n" + e.toString());
			increaseTried(goals.length);
		}

		try {
			try {
				coq.stop();
			}
			catch(Exception en) {
				
			}
			coq = CoqUtils.createNewCoqTop();
			coq.restart();
			coq.sendCommand("Require Import Bool.");
			coq.sendCommand("Require Import ZArith.");
			coq.sendCommand("Require Import Classical.");
			coq.sendCommand("Add LoadPath \"" + libFile.substring(0, libFile.lastIndexOf(File.separator)) + "\".");
			coq.sendCommand("Require Import \"" + fLibName + "_classes\".");						
			coq.sendCommand("Load \"user_extensions.v\".");
			coq.sendCommand("Require Import \"" + fLibName + "\".");
		
			coq.sendCommand("Import JackLogic.");
			coq.sendCommand("Open Scope Z_scope.");
			coq.sendCommand("Open Scope J_Scope.");
			//coq.resetSection("JackProof");
		} catch (AProverException e1) {
			//Logger.get().println(e1);
		}
	}

	
	/**
	 * Tries to prove the given goal
	 * @param name The name of the goal.
	 * @param g The goal to prove
	 * @return true if the proof was a success.
	 * @throws ProverException If there was a big problem during the proof.
	 */
	protected boolean proveLemma(String name, Goal g) 
			throws AProverException {
		boolean res = false;
		CoqTranslationResult ctr;
		HashMap vars = CoqLanguage.getNames();
		try {
			ctr = (CoqTranslationResult) g.getFormula().toLang("Coq", 0);

			res = tryTactic(name, ctr);
		} catch (LanguageException e) {
			// it should not happen...
			e.printStackTrace();
		} 
		CoqLanguage.resetNames(vars);
		return res;
	}

	
	/**
	 * Try the tactics on the current goal.
	 * @param ctr
	 * @param name
	 * @return true if the goal has been solved
	 * @throws ProverException if there was a big problem
	 */
	private boolean tryTactic(String name, CoqTranslationResult ctr) throws AProverException {
		boolean result = false;
		for (int i = 0;(!result) && (i < myTactics.length); i++) {
				coq.declareLemma(name, ctr.getForAllDecl(), "autoJack; arrtac.");
				result = playTactic(myTactics [i]);
				if(!result) coq.abort();
		}
		coq.clearBuffer();
		return result;
	}
	
	
	/**
	 * Try a tactic on the current goal.
	 * @param tactic The list of tactics to try.
	 * @return true if the tactic solved the goal.
	 * @throws ProverException if something dreadful has happened. 
	 */
	private boolean playTactic(String [] tactic) throws AProverException {
		boolean result = false;
		try {
			for (int i = 0; i < tactic.length; i++) {
				coq.sendCommand(tactic[i]);
				Logger.get().println(coq.getStdBuffer());
			}
			coq.qed();
			
			coq.clearBuffer();
			result = true;
		}catch (ToplevelException e) {
			//Logger.get().println("I am so broken in the realm of maldoror.");
			coq.doBreak();
			result = false;
			coq.restart();
		} catch (ProverException e) {
			coq.clearBuffer();
			result = false;
			coq.restart();
		} 
		return result;
	}
	

	/**
	 * The array containing the tactics to apply.
	 * @return The tactics to apply
	 */
	public abstract String [][]getTactics();


	/**
	 * Add an error to the error count.
	 * @param description The error description.
	 */
	private void addError(String description) {
		// append the error to the list of errors
		if (errors == null) {
			errors = description;
		} else {
			errors += "\n" + description;
		}

	}

	
	/**
	 * Return the name of the prover we are using.
	 * @return a string identifying the current prover tried.
	 */
	public abstract String getProverName();
	
	public File getJpoDir() {
		return dir;
	}
	
}
