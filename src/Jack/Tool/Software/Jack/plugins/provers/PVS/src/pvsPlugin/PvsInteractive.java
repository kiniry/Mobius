//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import jack.plugin.perspective.ICaseExplorer;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

import jml2b.exceptions.LanguageException;
import jpov.IInteractiveProver;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.TreeObject;
import jpov.structure.VirtualFormula;

import org.eclipse.jface.action.Action;

/**
 * @author L. Burdy
 **/
public class PvsInteractive extends Action implements IInteractiveProver {

	ICaseExplorer explorer;
	String outputDirectory;

	public IInteractiveProver factory(ICaseExplorer caseExp) {
		PvsInteractive res = new PvsInteractive();
		res.explorer = caseExp;
		res.setText("with PVS");
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
			String file = ((JmlFile) p).getJpoFile().getName();
			file = file.substring(0, file.indexOf('.'));
			try {
				File f =
					File.createTempFile(
						l.getName() + "Goal" + g.getNumber() + "_",
						".pvs",
						((JmlFile) p).getJpoFile().getParentFile());
				BufferedOutputStream ostream =
					new BufferedOutputStream(new FileOutputStream(f));
				PrintStream stream = new PrintStream(ostream);
				stream.println("T0 : THEORY");
				stream.println("BEGIN");
				stream.println(
					"mylib : LIBRARY = \"" + PvsPlugin.getLocation() + "div\"");
				stream.println("IMPORTING mylib@div, mylib@rem");
				stream.println("IMPORTING " + file + "_prelude");
				try {
					PvsTranslationResult ctr =
						(PvsTranslationResult) g.getFormula().toLang("PVS", 0);
					PvsTranslationResult ptr = getLemmasHypothesis(l);
					String str =
						(ptr.getLocalDecl() == null ? "" : ptr.getLocalDecl());
					str
						+= (ctr.getLocalDecl() == null ? "" : ctr.getLocalDecl());
					stream.println(str + "\nt0: CONJECTURE");
					stream.println(ptr.toUniqString() + "=>");
					stream.println(ctr.toUniqString() + "\n");
				} catch (LanguageException le) {
					stream.println("%" + le.getMessage());
				} catch (InternalError e) {
					stream.println("%" + e.getMessage());
				}
				stream.println("END T0");

				stream.close();
				ostream.close();
			    String[] cmd = (PvsPlugin.getPvsExe()  + " " + f.getAbsolutePath()).split("\\s");

//				String[] cmd = { PvsPlugin.getPvsExe(), f.getAbsolutePath()};
				Runtime.getRuntime().exec(cmd);
			} catch (IOException ioe) {
				;
			}
		}
	}

	private PvsTranslationResult getLemmasHypothesis(Lemma l)
		throws LanguageException {
		PvsTranslationResult res = null;
		for (int i = 0; i < l.getHyp().length; i++) {
			VirtualFormula vf = (VirtualFormula) l.getHyp()[i];
			PvsTranslationResult ctr =
				(PvsTranslationResult) vf.getF().toLang("PVS", 0);
			if (res == null)
				res = ctr;
			else
				res =
					new PvsTranslationResult(
						ctr,
						res,
						res.toUniqString() + " =>\n" + ctr.toUniqString());
		}
		return res;
	}

}
