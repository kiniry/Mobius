//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin;

import jack.plugin.perspective.ICaseExplorer;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jpov.IInteractiveProver;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.TreeObject;
import jpov.structure.VirtualFormula;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.progress.UIJob;

import prover.exec.AProverException;
import prover.gui.jobs.ProverStatus;
import coqPlugin.language.CoqVar;
import coqPlugin.printers.StaticPrelude2;
import coqPlugin.prooftask.util.CoqIdeThread;
import coqPlugin.prooftask.util.CoqPrintStream;

/**
 * @author L. Burdy and J. Charles
 */
public class CoqInteractive extends Action implements IInteractiveProver {

	private static String tacPure1;
	private static String tacPure2;
	ICaseExplorer explorer;
	String outputDirectory;

	public IInteractiveProver factory(ICaseExplorer caseExp) {
		CoqInteractive res = new CoqInteractive();
		res.explorer = caseExp;
		res.setText("with Coq");
		return res;
	}

	public void run() {
		Object[] tis = explorer.getTreeSelection();
		
		if (tis[0] instanceof Goal) {
			Goal g = (Goal) tis[0];
			Lemma l = (Lemma) g.getParent();
			TreeObject p = l;
			while (!(p instanceof JmlFile))
				p = (TreeObject) p.getParent();
			String file = ((JmlFile) p).getJpoFile().getAbsolutePath();
			file = file.substring(0, file.indexOf('.'));
			new CoqInteractiveJob(this, file, g, l).schedule();
			
		}
	}
	
	
	private class CoqInteractiveJob extends Job {
		String file;
		Goal g;
		Lemma l;
		CoqInteractive ci;
		File f;
		public CoqInteractiveJob(CoqInteractive ci, String file, Goal g,Lemma l) {
			super("Getting lemma");
			this.file = file;
			this.g = g;
			this.l = l;
			this.ci = ci;
		}

		protected IStatus run(IProgressMonitor monitor) {
			try {
				//ProverCoqStatus state = (ProverCoqStatus)g.getState().getProverStatus("Coq");
				String f1 = file.substring(0, file.lastIndexOf(File.separatorChar));
				File dir = new File( f1 + File.separator +"proofs" + File.separator);
				dir.mkdir();
				f = new File (dir +  File.separator  + CoqFile.getNameFromGoal(g));
				String proof;
				if(f.exists()) {
					proof = new CoqFile(f).getProof();
					if(proof.equals(""))
						proof = "(* Write your proof here *)\nstartJack.\n";
				}
				else 
					proof="(* Write your proof here *)\nstartJack.\n";
				PrintStream stream = new PrintStream(new BufferedOutputStream(new FileOutputStream(f)));
				try {
					writeCoqToStream(stream, file, l, g, proof);
					stream.close();
					new UIJob("Ide thread") {

						public IStatus runInUIThread(IProgressMonitor monitor) {
							new CoqIdeThread(ci, g, f, explorer);
							return ProverStatus.getOkStatus();
						}
						
					}.schedule();
				}
				catch (LanguageException le) {
					ProverStatus.getErrorStatus("Language exception", le);
					le.printStackTrace();
				}
				
				
			} catch (IOException ioe) {
				ProverStatus.getErrorStatus("IO exception", ioe);
				ioe.printStackTrace();
			}
			return ProverStatus.getOkStatus();
		}
		
	}
	

	public void writeCoqToStream(PrintStream out, String file, Lemma l, Goal g, String oldproof) 
			throws LanguageException {
		
		try {
			CoqPrintStream stream = new CoqPrintStream(out);
			printfile(stream, file, l, g, oldproof);
		} catch (AProverException e) {
			throw new LanguageException(e.getMessage());
		}
		
	}
	public void printfile(CoqPrintStream stream, String file, Lemma l, Goal g, String oldproof) {
		try {
			
			stream.println("Require Import Bool.");
			stream.println("Require Import ZArith.");
			stream.println("Require Import Classical.");
			//stream.println("Require Import Zdiv.");
//			if(PreferencePage.getCoqUseDumbStylePrelude()) {
//				stream.println("Load \"" + 
//						file
//						+ ".v\".\n");
//			}
//			else {
			stream.println("Add LoadPath \"" + file.substring(0, file.lastIndexOf(File.separator)) + "\".");
			String name = file.substring(file.lastIndexOf(File.separator) + 1);
			stream.println("Require Import \"" + name + "_classes\".");

//			}
			
			stream.println("Load \"user_extensions.v\".");
//			stream.println(
//					"Module UserExt := UserExtensions "+ name + "Classes.");
//			stream.println("Import UserExt.");
			stream.println("Require Import \"" + StaticPrelude2.fileName + "\".");
			stream.println("Require Import \"" + name + "\".");

			stream.println("Import JackLogic.");
			
			stream.println("Open Scope Z_scope.");
			stream.println("Open Scope J_Scope.\n");
			//stream.println("\n(* You can modify the following lines... *)\n");
			//stream.println("(* ... End of modification zone. *)\n");		
			CoqTranslationResult ctr =
				(CoqTranslationResult) g.getFormula().toLang("Coq", 0);
			stream.println("Section JackProof.\n");
			CoqLanguage.resetNames();
			CoqVar.setPrefix(l);
			List a = getLemmasHypothesisList(l);
			
			Iterator i = a.iterator();
			while(i.hasNext()) {
				try {
					String curr = (String) i.next();
					stream.prettyprint(curr.substring(0, curr.indexOf(' ') + 1), curr + "\n");
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			stream.println();
			if(tacPure1 != null) {
				stream.println(tacPure1);
				stream.println(tacPure2);
				stream.println("Ltac autoJ := unfold_pure_all; autoJack; arrtac.");
			}
			else {
				stream.println("Ltac autoJ := autoJack; arrtac.");
			}
			
			if(tacPure1 != null) {
				stream.println("Ltac purify := unfold_pure_all; simpl_pure.\n");
			}				
			else {
				stream.println("Ltac purify := simpl_pure.\n");
			}

			stream.pp_goal("\nLemma l:\n" +
					ctr.getForAllDecl() + ".");
			stream.simplprint("Proof with autoJ.\n" + oldproof +"\nQed.");
			stream.simplprint("End JackProof.");
			} catch (Exception e) {
				stream.simplprint("(* An Error has occured while processing the lemma *)");
				stream.simplprint(e.getMessage());
			} 
	}
	/**
	 * @deprecated
	 * @param l
	 * @return
	 * @throws LanguageException
	 */
	public static String getLemmasHypothesis(Lemma l) throws LanguageException {
		List list = getLemmasHypothesisList(l);
		Iterator i = list.iterator();
		String result = "";
		while(i.hasNext()) {
			String str = (String) i.next();
			result += str + "\n";
		}
		return result;
		
	}
	
	
	public static List getLemmasHypothesisList(Lemma l) throws LanguageException {
		VirtualFormula [] fTab = l.getHyp();
		CoqVar.setPrefix(l);
		List li = getLemmasHypothesisList(fTab);
		CoqVar.setPrefix(null);
		return li;
	}
	public static List getLemmasHypothesisList(VirtualFormula [] fTab) throws LanguageException {
		ArrayList listePure = new ArrayList();
		ArrayList listePureTac = new ArrayList();
		ArrayList listeVar = new ArrayList();
		ArrayList listeInv= new ArrayList();
		ArrayList listeHyp = new ArrayList();
		ArrayList listeReq = new ArrayList();
		int hyp_count = 1;
		int inv_count = 1;
		int req_count = 1;
		tacPure1 = null;
		tacPure2 = null;
		for (int i = 0; i < fTab.length; i++) {
			Formula current = fTab[i].getF();
			
			try {
				//Formula [] tab = ea.transform(current);
				CoqTranslationResult ctr =
					(CoqTranslationResult) current.toLang("Coq", 0);
				if(ctr.isVariableDecl()){
					String str = ctr.toString();
					if (!(str.lastIndexOf('(') != str.indexOf('('))) {
						// il y a une seule expression parenthesee
						str = str.substring(1, str.length() - 1);
					}
					listeVar.add("Variable " + str  + ".");	
				}
				else {
					if(current instanceof DeclPureMethodForm) {
						
						listePureTac.add(ctr.getPropPart());
						ctr.clearPropPart();
						String s = ctr.toString();
						listePure.add(s + ".");

					}
					else if(current.getNodeType() == IFormToken.LOCAL_ELEMENTS_DECL) {
						String str = ctr.getLocalDecl();
						if (!(str.lastIndexOf('(') != str.indexOf('('))) {
							// il y a une seule expression parenthesee
							str = str.substring(1, str.length() - 1);
						}
						listeVar.add("Variable " + str  + ".");		
						String s = ctr.toString();
						listeHyp.add("Hypothesis hyp" + hyp_count++ + " : " + s + ".");
					}
					
					else {
						
						String s = ctr.getForAllDecl();
						byte origin = fTab[i].getOrigin();
						if((origin == jml2b.pog.lemma.VirtualFormula.INVARIANT) ||
								(origin == jml2b.pog.lemma.VirtualFormula.STATIC_FINAL_FIELDS_INVARIANT)) {
							listeInv.add("Hypothesis inv" + inv_count++ + " : " + s + ".");
						}
						else if (origin == jml2b.pog.lemma.VirtualFormula.REQUIRES){
							listeReq.add("Hypothesis req" + req_count++ + " : " + s + ".");
						}
						else {
							listeHyp.add("Hypothesis hyp" + hyp_count++ + " : " + s + ".");
						}
						
					}
				}
			
			} catch (InternalError ie) {
				listeHyp.add("Variable hyp" + i + " : (* There was an error: " + ie.getMessage() + "*) True.");
			}
		}
		
		Iterator i = listePureTac.iterator();

		if(i.hasNext()) {
			tacPure1 = "Ltac unfold_pure H := unfold ";
			tacPure1 += i.next();
			while (i.hasNext()) {
				tacPure1 += ", ";
				tacPure1 += i.next();
			}
			tacPure1 += " in H.";
		}
		
		i = listePureTac.iterator();
		if(i.hasNext()) {
			tacPure2 = "Ltac unfold_pure_all := unfold ";
			tacPure2 += i.next();
			while (i.hasNext()) {
				tacPure2 += ", ";
				tacPure2 += i.next();
			}
			tacPure2 += " in *.";
		}
		
		
		listeReq.addAll(listeHyp);
		listeInv.addAll(listeReq);
		listePure.addAll(listeInv);
		listeVar.addAll(listePure);
		return listeVar;
	}

}
