//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: PmiPrinter
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package bPlugin;

import java.io.PrintStream;

import jpov.structure.Class;
import jpov.structure.Goal;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.Method;
import jpov.structure.Proofs;

/**
 * This class provides facilities to write a Atelier B pmi file.
 * The pmi file contains four theories: 
 * <UL>
 * <li>BalanceX contains the proof status for the file and for each operations
 * <li>ProofState contains the proof status of each lemma
 * <li>MethodList contains the proof script of each lemma
 * <li>PassList contains the tried proof force for each lemma
 * </UL>
 * @author L. Burdy
 **/
public class PmiPrinter {

	/**
	 * The print stream corresponding to the file
	 **/
	private PrintStream stream;

	private boolean firstItem;

	/**
	 * Constructs a pmi printer from an existing file printer and a print stream.
	 * @param fp The already existing file printer
	 * @param ps The print stream
	 **/
	public PmiPrinter(PrintStream ps) {
		stream = ps;
	}

	/**
	 * Prints the theory BalanceX of a JML file.
	 * @param f The JML file
	 **/
	public void printTheoryBalanceX(String name, JmlFile f) {
		stream.println("THEORY BalanceX IS");
		stream.print(name + "," + f.getNbPo() + ",0,0,0,0,0,0");
		printBalanceX(f.getClasses());
		stream.println("");
		stream.println("END &");
	}

	/**
	 * Prints the proof status of the methods of a set of classes.
	 * @param e The set of classes
	 **/
	private void printBalanceX(Class[] ca) {
		for (int i = 0; i < ca.length; i++)
			printBalanceX(ca[i]);
	}

	private int getNbPoProved(Lemma l, int force) {
		int res = 0;
		for (int i = 0; i < l.getGoals().length; i++) {
			Goal g = l.getGoals()[i];
			ProverBStatus pbs = (ProverBStatus) g.getProverStatus("B");
			if (pbs.isProved(force))
				res++;
		}
		return res;
	}

	private int getNbPoProved(Proofs p, int force) {
		int res = 0;
		for (int i = 0; i < p.getLemmas().length; i++) {
			res += getNbPoProved(p.getLemmas()[i], force);
		}
		return res;
	}

	private int getNbPoProved(Method m, int force) {
		return getNbPoProved(m.getLemmas(), force)
			+ getNbPoProved(m.getWellDefinednessLemmas(), force);
	}

	/**
	 * Prints the proof status of the static initialization and the methods of a 
	 * class.
	 * @param e The set of classes
	 **/
	private void printBalanceX(Class c) {
		for (int i = 0; i < c.getMethods().length; i++)
			printBalanceX(c.getMethods()[i]);
		for (int i = 0; i < c.getConstructors().length; i++)
			printBalanceX(c.getConstructors()[i]);
		stream.println(";");
		stream
			.print(
				c.getName()
				+ "_Static_Initialisation,"
				+ ((c.getStaticInitLemmas() == null
					? 0
					: c.getStaticInitLemmas().getNbPo())
					+ c.getWellDefInvLemmas().getNbPo())
				+ ","
				+ ((c.getStaticInitLemmas() == null
					? 0
					: getNbPoProved(
						c.getStaticInitLemmas(),
						ProverBStatus.PROVEDUTIL))
					+ getNbPoProved(
						c.getWellDefInvLemmas(),
						ProverBStatus.PROVEDUTIL))
				+ ",0," // I don't know the semantic of this number !!!
		+ (
			(c.getStaticInitLemmas() == null
				? 0
				: getNbPoProved(c.getStaticInitLemmas(), 0))
				+ getNbPoProved(c.getWellDefInvLemmas(), 0))
			+ ","
			+ ((c.getStaticInitLemmas() == null
				? 0
				: getNbPoProved(c.getStaticInitLemmas(), 1))
				+ getNbPoProved(c.getWellDefInvLemmas(), 1))
			+ ","
			+ ((c.getStaticInitLemmas() == null
				? 0
				: getNbPoProved(c.getStaticInitLemmas(), 2))
				+ getNbPoProved(c.getWellDefInvLemmas(), 2))
			+ ","
			+ ((c.getStaticInitLemmas() == null
				? 0
				: getNbPoProved(c.getStaticInitLemmas(), 3))
				+ getNbPoProved(c.getWellDefInvLemmas(), 3)));

	}

	/**
	 * Prints the proof status of a method.
	 * @param m The method
	 **/
	private void printBalanceX(Method m) {
		stream.println(";");
		stream
			.print(
				m.getPmiName()
				+ ","
				+ m.getNbPo()
				+ ","
				+ getNbPoProved(m, ProverBStatus.PROVEDUTIL)
				+ ",0" // I don't know the semantic of this number !!!
		+","
			+ getNbPoProved(m, 0)
			+ ","
			+ getNbPoProved(m, 1)
			+ ","
			+ getNbPoProved(m, 2)
			+ ","
			+ getNbPoProved(m, 3));
	}

	/**
	 * Prints the theory ProofState of a JML file.
	 * @param f The JML file
	 **/
	public void printTheoryProofState(JmlFile f) {
		stream.println("THEORY ProofState IS");
		firstItem = true;
		for (int i = 0; i < f.getClasses().length; i++)
			printProofState(f.getClasses()[i]);
		stream.println("");
		stream.println("END &");
	}

	/**
	 * Prints the proof status of a class.
	 * @param e the class
	 **/
	private void printProofState(Class c) {
		for (int i = 0; i < c.getMethods().length; i++)
			printProofState(c.getMethods()[i]);
		for (int i = 0; i < c.getConstructors().length; i++)
			printProofState(c.getConstructors()[i]);
		if (c.getStaticInitLemmas() != null)
			printProofState(c.getStaticInitLemmas());
		printProofState(c.getWellDefInvLemmas());
	}

	/**
	 * Prints the proof status of a set of method.
	 * @param e the set of method
	 **/
	private void printProofState(Method m) {
		printProofState(m.getLemmas());
		printProofState(m.getWellDefinednessLemmas());
	}

	/**
	 * Prints the proof status of a set of lemmas.
	 * @param lv the set of lemmas
	 **/
	private void printProofState(Proofs lv) {
		for (int i = lv.getLemmas().length - 1; i >= 0; i--) {
			printProofState(lv.getLemmas()[i]);
		}
	}

	/**
	 * Prints the proof status of a lemma (a set of goals).
	 * @param l the lemma
	 **/
	private void printProofState(Lemma l) {
		for (int i = l.getNbPo() - 1; i >= 0; i--) {
			Goal g = l.getGoals()[i];

			if (firstItem)
				firstItem = false;
			else
				stream.println(";");
			stream.print(((ProverBStatus) g.getProverStatus("B")).getProveState());
		}
	}

	/**
	 * Prints the theory MethodList of a JML file.
	 * @param f The JML file
	 **/
	public void printTheoryMethodList(JmlFile f) {
		stream.println("THEORY MethodList IS");
		firstItem = true;
		for (int i = 0; i < f.getClasses().length; i++)
			printMethodList(f.getClasses()[i]);
		stream.println("");
		stream.println("END &");
	}

	/**
	 * Prints the theory MethodList of a class
	 * @param a The class
	 **/
	private void printMethodList(Class c) {
		for (int i = 0; i < c.getMethods().length; i++)
			printMethodList(c.getMethods()[i]);
		for (int i = 0; i < c.getConstructors().length; i++)
			printMethodList(c.getConstructors()[i]);
		if (c.getStaticInitLemmas() != null)
			printMethodList(c.getStaticInitLemmas());
		printMethodList(c.getWellDefInvLemmas());
	}

	/**
	 * Prints the theory MethodList of a set of method
	 * @param e The set of method
	 **/
	private void printMethodList(Method m) {
		printMethodList(m.getLemmas());
		printMethodList(m.getWellDefinednessLemmas());
	}

	/**
	 * Prints the theory MethodList of a proof
	 * @param lv the proof
	 **/
	private void printMethodList(Proofs lv) {
		for (int i = lv.getLemmas().length - 1; i >= 0; i--) {
			Lemma l = lv.getLemmas()[i];
			printMethodList(l);
		}
	}

	/**
	 * Prints the theory MethodList of a lemma
	 * @param l The lemma
	 **/
	private void printMethodList(Lemma l) {
		for (int i = l.getNbPo() - 1; i >= 0; i--) {
			Goal g = l.getGoals()[i];
			if (firstItem)
				firstItem = false;
			else
				stream.println(";");
			ProverBStatus pbs = (ProverBStatus) g.getProverStatus("B");
			if (pbs.isProved()
				&& pbs.getProveForce() == ProverBStatus.PROVEDUTIL)
				stream.print(pbs.getMethodList());
			else
				stream.print("pr");
		}
	}

	/**
	 * Prints the theory PassList of a JML file.
	 * @param f The JML file
	 **/
	public void printTheoryPassList(JmlFile f) {
		stream.println("THEORY PassList IS");
		boolean first = true;
		for (int i = 0; i < f.getNbPo(); i++) {
			if (first)
				first = false;
			else
				stream.println(";");
			stream.print("Force(0),?");
		}
		stream.println("");
		stream.println("END");
	}

}
