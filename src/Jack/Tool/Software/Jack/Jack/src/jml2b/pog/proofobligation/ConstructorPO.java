//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ConstructorPO
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.proofobligation;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.substitution.SubInstancesSingle;
import jml2b.pog.substitution.SubTypeofSingle;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.Method;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Statement;

/**
 * This class describes proof obligations for a constructor and facilities 
 * to calculate them.
 * @author L. Burdy
 */
public class ConstructorPO extends MethodPO {

	/**
	 * Constructs a proof obligation
	 * @param c The current class
	 * @param s The name suffix
	 * @param m The current method
	 * @param h1 The invariant
	 * @param h2 The requires 
	 * @param box The colored info
	 * @param b The body
	 * @param p1 The normal behaviour proof
	 * @param p7 The exceptional behaviour proof
	 **/
	/*@
	  @ requires b != null;
	  @ requires c != null;
	  @ requires m != null;
	  @ requires h1 != null;
	  @ requires h2 != null;
	  @*/
	public ConstructorPO(
		Class c,
		String s,
		Method m,
		FormulaWithSpecMethodDecl h1,
		FormulaWithSpecMethodDecl h2,
		ColoredInfo box,
		Statement b,
		Theorem p1,
		Theorem p7) {
		super(c.getBName() + "_" + s, c, m,h1, h2, box, b, p1, p7);
	}

	public void pog(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		ExceptionalBehaviourStack ebs =
			new ExceptionalBehaviourStack(new ExceptionalProofs(getPhi7()));

		getPhi1().oldParam(((Parameters) getMethod().getParams()).signature);
		Proofs p = new Proofs(getPhi1());
		p.sub(
			new SubTypeofSingle(
				new TerminalForm(Ja_LITERAL_this, "this"),
				new TTypeForm(
					IFormToken.Jm_T_TYPE,
					new Type(getMethod().getDefiningClass()))));
		p.sub(
			new SubInstancesSingle(new TerminalForm(Ja_LITERAL_this, "this")));

		getMethod().lemmas = getBody().ensures(config, p, ebs);

		//		getMethod().lemmas.sub(
		//			new SubTypeofSingle(
		//				new TerminalForm(Ja_LITERAL_this, "this"),
		//				new TTypeForm(new Type(getMethod().definingClass))));
		//		getMethod().lemmas.sub(
		//			new SubInstancesSingle(new TerminalForm(Ja_LITERAL_this, "this")));

		getMethod().lemmas.addHyp(
			BinaryForm.getDefaultRefDecl(
				new TerminalForm(Ja_LITERAL_this, "this")));
		getMethod().lemmas.addHyp(
			new BinaryForm(
				LOCAL_VAR_DECL,
				new TerminalForm(Ja_LITERAL_this, "this"),
				TerminalForm.$References));

		finalizePog(config);
	}

}
