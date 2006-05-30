//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: MchPrinter
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
import jml2b.structure.IClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;

/**
 * This class provides facilities to write a B machine that have the same lemmas
 * as those generated derectly into the PO file. The machine declares sets, 
 * constants, properties and assertions.
 * @author L. Burdy
 **/
public class MchPrinter {

	BPrinter printer;
	PrintStream stream;

	/**
	 * Constructs a mach printer from an existing file printer and a print 
	 * stream.
	 * @param fp The already existing file printer
	 * @param ps The print stream
	 **/
	public MchPrinter(BPrinter fp, PrintStream ps) {
		printer = fp;
		stream = ps;
	}

	/**
	 * Prints the machine header, that is the clauses MACHINE and SETS for a JML 
	 * file.
	 * @param jf The JML file
	 **/
	public void printMchHeader(IJml2bConfiguration config, JmlFile jf) {
		stream.println("MACHINE");
		stream.println("   " + jf.getFlatName( config.getPackage()) + "\n");
		stream.println("SETS");
		stream.println("   REFERENCES;");
		stream.println("   t_float;");
		stream.print("  " + BPrinter.NAMES + " = {");

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
		stream.println("}\n");
	}

	/**
	 * Prints the ABSTRACT_CONSTANTS clause. This clause declares all the 
	 * constants concerning builtin types, functions j_xxx, xxxelements ...
	 **/
	public void printConstants(IJml2bConfiguration config) throws LanguageException {
		stream.println("ABSTRACT_CONSTANTS");
		stream.println("c_minint,");
		stream.println("c_maxint,");
		stream.println("c_minshort,");
		stream.println("c_maxshort,");
		stream.println("c_minbyte,");
		stream.println("c_maxbyte,");
		stream.println("c_minchar,");
		stream.println("c_maxchar,");
		stream.println("c_minlong,");
		stream.println("c_maxlong,");
		stream.println("t_int,");
		stream.println("t_short,");
		stream.println("t_byte,");
		stream.println("t_char,");
		stream.println("t_long,");
		stream.println("j_add,");
		stream.println("j_sub,");
		stream.println("j_mul,");
		stream.println("j_div,");
		stream.println("j_rem,");
		stream.println("j_neg,");
		stream.println("j_shl,");
		stream.println("j_shr,");
		stream.println("j_ushr,");
		stream.println("j_and,");
		stream.println("j_or,");
		stream.println("j_xor,");
		stream.println("j_int2char,");
		stream.println("j_int2byte,");
		stream.println("j_int2short,");
		IClass string = config.getPackage().getJavaLangString();
		if (string != null) {
			stream.println("j_string,");
		}
		stream.println("null,");
		stream.println("subtypes,");
		stream.println("instances,");
		stream.println("typeof,");
		stream.println("arraylength,");
		stream.println("intelements,");
		stream.println("charelements,");
		stream.println("shortelements,");
		stream.println("byteelements,");
		stream.println("booleanelements,");
		stream.println("refelements,");
		stream.println("flatran,");
		stream.print("elemtype");
		printFieldTypes();
		stream.println("\n");
	}

	/**
	 * Prints a field declaration into the ABSTRACT_CONSTANTS clause.
	 * @param f The field.
	 **/
	void printFieldType(AField f) {
		if (f.garbage) {
			// ignore fields which do not appear in lemmas
			return;
		}

		// get the type of the field
		Type t = f.getType();

		// ignore double and long field
		if (t.getTag() == Type.T_DOUBLE || t.getTag() == Type.T_LONG)
			return;

		// ignore static final fields that are expanded
		if (f.isExpanded())
			return;

		stream.print(",\n" + f.getBName());
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
	/**
	 * Prints the PROPERTIES and the DEFINITIONS clauses.
	 * @param config The current configuration
	 * @param jf The currently treated jml file
	 **/
	public void printProperties(IJml2bConfiguration config, JmlFile jf)
		throws LanguageException {
		stream.println("PROPERTIES");
		printer.printJvaluesProperties();
		printer.printJml2bDefs(config, true);
		printer.printSubtypes(config);
		printFieldTypes();
		stream.println("\nDEFINITIONS");
		printer.firstItem = true;
		printFormulasDef(jf.getClasses(), 2);
		stream.println("\n");
	}

	/**
	 * Prints the formulas that appears in lemmas as definitions.
	 * @param e The set of classes where formulas are extracted
	 * @param cpt The formula counter, usefull to give an uniq name to 
	 * definitions
	 **/
	private void printFormulasDef(Enumeration e, int cpt)
		throws LanguageException {
		while (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			cpt = printFormulasDef(c, cpt);
		}
	}

	/**
	 * Prints the formulas that appears in lemmas of a class as definitions.
	 * @param c The class where formulas are extracted
	 * @param cpt The formula counter, usefull to give an uniq name to 
	 * definitions
	 * @return the current formula counter.
	 **/
	private int printFormulasDef(Class c, int cpt) throws LanguageException {
		if (c.getStaticInitLemmas() != null)
			cpt = printer.printFormulas(c.getStaticInitLemmas(), cpt);
		cpt = printer.printFormulas(c.getWellDefInvLemmas(), cpt);
		Enumeration e = c.getConstructors();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			cpt = printFormulasDef(m.lemmas, cpt);
			cpt = printFormulasDef(m.wellDefinednessLemmas, cpt);
		}
		e = c.getMethods();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			cpt = printFormulasDef(m.getLemmas(), cpt);
			cpt = printFormulasDef(m.getWellDefinednessLemmas(), cpt);
		}
		return cpt;
	}

	/**
	 * Prints the formulas that appears in lemmas of a proof as definitions.
	 * @param p The proof where formulas are extracted
	 * @param cpt The formula counter, usefull to give an uniq name to 
	 * definitions
	 * @return the current formula counter.
	 **/
	private int printFormulasDef(Proofs p, int cpt) throws LanguageException {
		if (p != null) {
			Enumeration e = p.getLocHyp();
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				if (p.isUsed(vf)) {
					Formula f = vf.getFormula();
					if (printer.firstItem)
						printer.firstItem = false;
					else
						stream.println(";");
					stream.print("f_" + cpt + " == (");
					stream.print(f.toLang("B", 0).toUniqString());
					stream.print(")");
					cpt++;
				}
			}
			for (int i = 0; i < p.nbLemmas() - 1; i++) {
				SimpleLemma l = p.getLemma(i);
				Enumeration e1 = l.getGoals();
				while (e1.hasMoreElements()) {
					NonObviousGoal g = (NonObviousGoal) e1.nextElement();
					if (printer.firstItem)
						printer.firstItem = false;
					else
						stream.println(";");
					stream.print("f_" + cpt + " == (");
					//TODO Traiter correctement les methodes pures
				stream.print(g.getFormula().toLang("B", 0).toUniqString());
					stream.print(")");
					cpt++;

				}
			}
		}
		return cpt;
	}

	/**
	 * Prints the ASSERTIONS clauses and the END that close the machine for a 
	 * JML file.
	 * @param jf The JML file
	 **/
	public void printAssertions(JmlFile jf) {
		stream.println("ASSERTIONS");
		printer.firstItem = true;
		printProofAssert(jf.getClasses());
		stream.println("\nEND");
	}

	/**
	 * Prints the assertions associated with a set of class
	 * @param e The set of classes
	 **/
	private void printProofAssert(Enumeration e) {
		if (e.hasMoreElements()) {
			Class c = (Class) e.nextElement();
			printProofAssert(e);
			printProofAssert(c);
		}
	}

	/**
	 * Prints the assertions associated to a class
	 * @param c The class
	 **/
	private void printProofAssert(Class c) {
		printProofMethodAssert("this", c.getMethods());
		printProofMethodAssert("this", c.getConstructors());
		//c.staticInitLemmas.nbPo();
		if (c.getStaticInitLemmas() != null)
			printProofAssert("", c.getStaticInitLemmas());
		//c.wellDefInvLemmas.nbPo();
		printProofAssert("", c.getWellDefInvLemmas());
	}

	/**
	 * Prints the assertions associated with a set of method
	 * @param decl The string containing the fields to quantify on
	 * @param e The set of method
	 **/
	private void printProofMethodAssert(String decl, Enumeration e) {
		if (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			String par = m.getParamsString();
			if (!decl.equals(""))
				if (!par.equals(""))
					par = decl + "," + par;
				else
					par = decl;

			printProofMethodAssert(decl, e);
			printProofAssert(par, m.getLemmas());
			printProofAssert(par, m.getWellDefinednessLemmas());
		}
	}

	/**
	 * Prints the assertions associated with a proof
	 * @param decl The string containing the fields to quantify on
	 * @param lv The proof
	 **/
	private void printProofAssert(String decl, Proofs lv) {
		if (lv == null)
			return;
		for (int i = lv.nbLemmas() - 1; i >= 0; i--) {
			Theorem t = lv.getTheorem(i);
			SimpleLemma l = lv.getLemma(i);
			printProofAssert(decl, t, l);
		}
	}

	/**
	 * Prints the assertions associated with a lemma
	 * @param decl The string containing the fields to quantify on
	 * @param t The theorem associated with the lemma
	 * @param l The lemma
	 **/
	private void printProofAssert(String decl, Theorem t, SimpleLemma l) {
		for (int i = l.nbPo() - 1; i >= 0; i--) {
			NonObviousGoal g = (NonObviousGoal) l.getGoal(i);
			if (printer.firstItem)
				printer.firstItem = false;
			else
				stream.println(";");
			if (!decl.equals(""))
				stream.print("!(" + decl + ").");
			stream.print("(");
			Enumeration e = t.getHyp().elements();
			boolean first = true;
			while (e.hasMoreElements()) {
				VirtualFormula vf = (VirtualFormula) e.nextElement();
				Formula f = vf.getFormula();
				if (printer.formulaRank.containsKey(f)) {
					if (!first)
						stream.print(" &");
					else
						first = false;

					stream.print(" f_" + printer.formulaRank.get(f).toString());
				}
			}
			if (!first)
				stream.print(" =>");
			stream.print(
				"f_"
					+ printer.formulaRank.get(g.getFormula()).toString()
					+ ")");
		}
	}

}
