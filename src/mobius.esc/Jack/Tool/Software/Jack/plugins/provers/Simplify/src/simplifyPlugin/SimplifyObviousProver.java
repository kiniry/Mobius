//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import java.io.File;
import java.util.Enumeration;

import jml2b.IJml2bConfiguration;
import jml2b.pog.IObviousProver;
import jml2b.pog.lemma.Goal;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyObviousProver implements IObviousProver {

	public void prove(IJml2bConfiguration config, JmlFile jmlfile) {
		ReadStream readStream = null;
		try {

			int nbPo = jmlfile.getNbPo();
			boolean[] results = new boolean[nbPo];
			// indicates that the proof starts

			int lemme = 1;
			int index = 0;
			int file = 0;
			String readS = "";
			Simplify simplify = null;
			while (lemme <= nbPo) {

				try {
					File f =
						new File(
							config.getSubdirectory(),
							jmlfile.getFlatName( config.getPackage()) + ".sim" + file++);
					if (!f.exists()) {
						return;
					}
					simplify =
						new Simplify(
							SimplifyPreferencePage.getSimplifyExe(),
							f.getAbsolutePath());
				} catch (SimplifyException e) {
					return;
				}

				readStream = new ReadStream(simplify);
				readStream.run();

				int tmpindexV, tmpindexI, tmpindexA;
				int currentLemma = 1;
				index = 0;
				readS = "";
				while (readStream.isAliv()) {
					String str;
					do {
						str = readStream.read(null);
					} while (str == null && readStream.isAliv());
					readS = readS.substring(index, readS.length());
					readS = readS + str;
					index = 0;
					while (true) {
						tmpindexV =
							readS.indexOf(currentLemma + ": Valid.", index);
						tmpindexI =
							readS.indexOf(currentLemma + ": Invalid.", index);
						tmpindexA = readS.indexOf("Bad input:", index);
						if (tmpindexV != -1
							&& (tmpindexI == -1 || tmpindexI > tmpindexV)
							&& (tmpindexA == -1 || tmpindexA > tmpindexV)) {
							results[lemme - 1] = true;
							lemme++;
							currentLemma++;
							index = tmpindexV + 1;
						} else if (
							tmpindexI != -1
								&& (tmpindexA == -1 || tmpindexA > tmpindexI)) {
							results[lemme - 1] = false;
							lemme++;
							currentLemma++;
							index = tmpindexI + 1;
						} else if (tmpindexA != -1) {
							lemme++;
							currentLemma++;
							index = tmpindexA + 1;
						} else
							break;
					}

				}
				readStream.stopped();
				// stops the simplify process
				simplify.stop();
			}

			// update the jpo file with the results.
			proveFile(jmlfile, results, 0);
		} catch (Exception e) {
			throw new jml2b.exceptions.InternalError(e.getMessage());
		} finally {
			if (readStream != null)
				readStream.stopped();
		}

	}

	private static void proveFile(JmlFile file, boolean[] results, int cpt) {
		Enumeration e = file.getClasses();
		while (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			cpt = proveClass(c, results, cpt);
		}
	}

	/**
	 * Tries to prove each of the lemmas associated to the class.
	 */
	//@ requires simplify != null;
	//@ requires c != null;
	private static int proveClass(Class c, boolean[] results, int cpt) {
		cpt = proveMethods(c.getMethods(), results, cpt);
		cpt = proveMethods(c.getConstructors(), results, cpt);
		if (c.getStaticInitLemmas() != null)
			cpt = proveProofs(c.getStaticInitLemmas(), results, cpt);
		return proveProofs(c.getWellDefInvLemmas(), results, cpt);

	}

	private static int proveMethods(
		Enumeration e,
		boolean[] results,
		int cpt) {
		if (e.hasMoreElements()) {
			Method m =
				(Method) e.nextElement();
			cpt = proveProofs(m.getLemmas(), results, cpt);
			cpt = proveProofs(m.getWellDefinednessLemmas(), results, cpt);
			return proveMethods(e, results, cpt);
		} else
			return cpt;
	}

	/**
	 * Tries to prove the given proof.
	 */
	//@ requires simplify != null;
	//@ requires p != null;
	private static int proveProofs(Proofs p, boolean[] results, int cpt) {
		if (p == null)
			return cpt;
		for (int i = 0; i < p.nbLemmas(); i++) {
			SimpleLemma l = p.getLemma(i);
			cpt = proveGoals(l.getGoals(), results, cpt);
		}
		return cpt;
	}

	private static int proveGoals(Enumeration e, boolean[] results, int cpt) {
		if (e.hasMoreElements()) {
			cpt = proveGoal((Goal) e.nextElement(), results, cpt);
			return proveGoals(e, results, cpt);
		} else
			return cpt;
	}
	//@ requires goals != null;
	private static int proveGoal(Goal goal, boolean[] results, int cpt) {
		goal.setObvious(results[cpt++]);
		return cpt;
	}

}
