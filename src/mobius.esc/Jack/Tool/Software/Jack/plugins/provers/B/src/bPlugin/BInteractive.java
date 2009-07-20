//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jack.plugin.perspective.ICaseExplorer;

import java.io.IOException;

import jpov.IInteractiveProver;

import org.eclipse.jface.action.Action;

/**
 * @author L. Burdy and J. Charles
 */
public class BInteractive extends Action implements IInteractiveProver {

	ICaseExplorer explorer;
	String outputDirectory;

	public IInteractiveProver factory(ICaseExplorer caseExp) {
		BInteractive res = new BInteractive();
		res.explorer = caseExp;
		res.setText("with Click'nProve");
		return res;
	}

	public void run() {
		try {
		Runtime.getRuntime().exec(BPlugin.getClicjNProveExe());
		}
		catch (IOException ioe) {
			
		}
//		Object[] tis = explorer.getTreeSelection();
//		
//		if (tis[0] instanceof Goal) {
//			Goal g = (Goal) tis[0];
//			Lemma l = (Lemma) g.getParent();
//			TreeObject p = l;
//			while (!(p instanceof JmlFile))
//				p = (TreeObject) p.getParent();
//			String file = ((JmlFile) p).getJpoFile().getAbsolutePath();
//			file = file.substring(0, file.indexOf('.'));
//			try {
//				ProverBStatus state = (ProverBStatus)g.getState().getProverStatus("Coq");
//				
//				File f = File.createTempFile("coqFromJack", ".v");
//				PrintStream stream = new PrintStream(new BufferedOutputStream(new FileOutputStream(f)));
//				if (state != null && !state.isUnknown())
//					state.writeCoqToStream(stream);
//				else
//					writeCoqToStream(stream, file, l, g);
//				stream.close();
//				new Thread(new CoqIdeThread(this, g, f, explorer)).start();
//			} catch (IOException ioe) {
//				;
//
//			} catch (LanguageException ioe) {
//				;
//			}
//		}
	}
}
