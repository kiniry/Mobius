//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: PoPrinter
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package bPlugin;

import java.io.PrintStream;
import java.util.Enumeration;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LanguageException;
import jml2b.formula.Formula;
import jml2b.pog.lemma.NonObviousGoal;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;

/**
 * This class provides facilities to write a Atelier B po file. A po file 
 * contains three theories: 
 * <UL>
 * <li>EnumerateX contains the declaration of the enumerate sets
 * <li>Formulas contains the declaration of all the formula that appears in the 
 * lemmas
 * <li>ProofList contains the list of all the lemmas, lemmas are described 
 * referencing the formulas of the Formulas theory
 * </UL>
 * @author L. Burdy
 **/
public class PoPrinter {

	PrintStream stream;
	BPrinter printer;

	/**
	 * Constructs a po printer from an existing file printer and a print stream.
	 * @param fp The already existing file printer
	 * @param ps The print stream
	 **/
	public PoPrinter(BPrinter bp, PrintStream ps) {
		stream = ps;
		printer = bp;
	}

	/**
	 * Prints the theory EnumerateX
	 **/
	public void printTheoryEnumerateX() {
		stream.println("THEORY EnumerateX IS");
		printNames();
		stream.println("END &");
	}

	/**
	 * Prints the NAMES enumerate
	 **/
	private void printNames() {

		stream.print("  " + BPrinter.NAMES + " == {");

		// print builtin types
		for (int i = 0; i < BPrinter.builtinNames.length; ++i) {
			if (i != 0)
				stream.print(",");
			stream.println(BPrinter.builtinNames[i]);
		}

		// print classes        
		int cpt =
			printer.printClasses(
				printer.getClasses(),
				BPrinter.builtinNames.length + 1);
		cpt = printer.printClasses(printer.getInterfaces(), cpt);
		cpt--;
		BPrinter.defTYPES = "(1.." + cpt + ")*{" + BPrinter.NAMES + "}*NATURAL";
		BPrinter.defARRAYS =
			"(1.." + cpt + ")*{" + BPrinter.NAMES + "}*(NATURAL-{0})";
		BPrinter.defNAMES = "(1.." + cpt + ")*{" + BPrinter.NAMES + "}";
		stream.println("}");
	}

	/**
	 * Prints the theory Formulas of a JML file.
	 * @param config The current configuration
	 * @param f The JML file
	 **/
	public void printTheoryFormulas(IJml2bConfiguration config, JmlFile f)
		throws LanguageException {
		stream.println("THEORY Formulas IS");
		stream.print("(");
		printer.printJvaluesProperties();
		printer.printJml2bDefs(config, false);
		printProperties(config);
		stream.print(")");
		printFormulas(f.getClasses(), 2);
		stream.println("");
		stream.println("END &");
	}

	/**
	 * Prints the formulas corresponding to subtype relation evaluation and 
	 * field declaration.
	 * @param config The current configuration
	 **/
	private void printProperties(IJml2bConfiguration config)
		throws LanguageException {
		printer.printSubtypes(config);
		// type parameters
		printFieldTypes();
	}

	/**
	 * Prints the formulas that appear in the lemmas of a set of classes
	 * @param e The set of classes
	 * @param cpt The formula counter usefull to set a formulaRank to each 
	 * formula
	 **/
	private void printFormulas(Enumeration e, int cpt) {
		while (e.hasMoreElements()) {
			jml2b.structure.java.Class c = (Class) e.nextElement();
			cpt = printFormulas(c, cpt);
		}
	}

	/**
	 * Prints the formulas that appear in the lemmas of a class
	 * @param c The class
	 * @param cpt The formula counter usefull to set a formulaRank to each 
	 * formula
	 **/
	private int printFormulas(Class c, int cpt) {
		if (c.getStaticInitLemmas() != null)
			cpt = printer.printFormulas(c.getStaticInitLemmas(), cpt);
		cpt = printer.printFormulas(c.getWellDefInvLemmas(), cpt);
		Enumeration e = c.getConstructors();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			cpt = printer.printFormulas(m.lemmas, cpt);
			cpt = printer.printFormulas(m.wellDefinednessLemmas, cpt);
		}
		e = c.getMethods();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			cpt = printer.printFormulas(m.getLemmas(), cpt);
			cpt = printer.printFormulas(m.getWellDefinednessLemmas(), cpt);
		}
		return cpt;
	}

	/**
	 * Prints the theory ProofList of a JML file.
	 * @param f The JML file
	 **/
	public void printTheoryProofList(JmlFile f) {
		stream.println("THEORY ProofList IS");
		printer.firstItem = true;
		printProof(f.getClasses());
		stream.println("");
		stream.println("END");
	}

	/**
	 * Prints into the theory ProofList, the lemmas of a set of classes.
	 * @param e The set of classes
	 **/
	private void printProof(Enumeration e) {
		if (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			printProof(e);
			printProof(c);
		}
	}

	/**
	 * Prints into the theory ProofList, the lemmas of a class.
	 * @param c The class
	 **/
	private void printProof(Class c) {
		printProofMethod(c.getMethods());
		printProofMethod(c.getConstructors());
		if (c.getStaticInitLemmas() != null)
			printProof(c.getStaticInitLemmas(), c.getStaticInitLemmas().nbPo());
		printProof(c.getWellDefInvLemmas(), c.getWellDefInvLemmas().nbPo());
	}

	/**
	 * Prints into the theory ProofList, the lemmas of a set of methods.
	 * @param e The set of methods
	 **/
	private void printProofMethod(Enumeration e) {
		if (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			printProofMethod(e);
			printProof(m.getLemmas(), m.getLemmas().nbPo());
			printProof(m.getWellDefinednessLemmas(), m.getWellDefinednessLemmas().nbPo());
		}
	}

	/**
	 * Prints lemmas into the theory ProofList.
	 * @param lv The lemmas
	 * @param counter The number of goals in the lemmas
	 **/
	private void printProof(Proofs lv, int counter) {
		if (lv == null)
			return;
		for (int i = lv.nbLemmas() - 1; i >= 0; i--) {
			Theorem t = lv.getTheorem(i);
			SimpleLemma l = lv.getLemma(i);
			counter = printProof(t, l, counter);
		}
		return;
	}

	/**
	 * Prints lemmas into the theory ProofList.
	 * @param t The theorem containing the lemmas
	 * @param l The lemmas
	 * @param counter The current number to associate to goals.
	 * @return The updated goal number.
	 **/
	private int printProof(Theorem t, SimpleLemma l, int counter) {
		for (int i = l.nbPo() - 1; i >= 0; i--) {
			NonObviousGoal g = (NonObviousGoal) l.getGoal(i);
			if (printer.firstItem)
				printer.firstItem = false;
			else
				stream.println(";");
			stream.print("  _f(1)");
			Enumeration e = t.getHyp().elements();
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				Formula f = vf.getFormula();
				if (vf.getOrigin() == VirtualFormula.INVARIANT
					&& printer.formulaRank.containsKey(f)) {
					stream.print(
						" & _f(" + printer.formulaRank.get(f).toString() + ")");
				}
			}

			stream.print(
				" & " + t.getName() + "." + g.setNumber(counter--) + ",(");
			e = t.getHyp().elements();
			boolean first = true;
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				Formula f = vf.getFormula();
				if (!(vf.getOrigin()
					== VirtualFormula.STATIC_FINAL_FIELDS_INVARIANT)
					&& !(vf.getOrigin() == VirtualFormula.INVARIANT)
					&& printer.formulaRank.containsKey(f)) {
					if (!first)
						stream.print(" &");
					else
						first = false;

					stream.print(
						" _f(" + printer.formulaRank.get(f).toString() + ")");
				}
			}
			if (!first)
				stream.print(" =>");
			stream.print(
				"_f("
					+ printer.formulaRank.get(g.getFormula()).toString()
					+ "))");
		}
		return counter;
	}

	/**
	 * Prints a field type declaration.
	 * @param f The field
	 **/
	void printFieldType(AField f) throws LanguageException {
		if (f.garbage) {
			// ignore fields which do not appear in lemmas
			return;
		}
		// get the type of the field
		Type t = f.getType();

		if (/*t.getTag() == Type.T_FLOAT
																																																																																																																															||*/
			t.getTag() == Type.T_DOUBLE || t.getTag() == Type.T_LONG)
			return;

		if (f.isExpanded())
			return;

		if (f.getModifiers().isStatic()) {
			// static field

			// print the name of the field
			stream.print("& " + f.getBName() + " : " + BPrinter.getBType(t));
			if (!t.isBuiltin()) {
				stream.print(
					"& (not("
						+ f.getBName()
						+ " = null) => "
						+ f.getBName()
						+ " : instances)");
				stream.print(
					"& (not("
						+ f.getBName()
						+ " = null) => typeof("
						+ f.getBName()
						+ ") : subtypes[{ "
						+ t.toLang("B").toUniqString()
						+ "}])");
			}
		} else {
			// member field
			stream.print(
				"& "
					+ f.getBName()
					+ " : "
					+ "typeof~[subtypes[{"
					+ printer.getBClass(BPrinter.getBClass(f.getDefiningClass()))
					+ "}]]"
					+ " --> "
					+ BPrinter.getBType(f.getType()));
		}
	}

	/**
	 * Prints fields type declaration.
	 * @param e The set of fields
	 **/
	private void printFieldTypes(Enumeration e) throws LanguageException {
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			printFieldType(f);
		}
	}

	/**
	 * Prints the fields of a set of classes type declaration.
	 * @param e The set of classes
	 **/
	private void printFieldTypesForClasses(Enumeration e)
		throws LanguageException {
		while (e.hasMoreElements()) {
			BClass c = (BClass) e.nextElement();
			printFieldTypes(c.getAc().getFields());
		}
	}

	/**
	 * Prints the field type declaration
	 **/
	private void printFieldTypes() throws LanguageException {
		printer.firstItem = true;
		printFieldTypesForClasses(printer.getClasses());
		printFieldTypesForClasses(printer.getInterfaces());
	}

}
