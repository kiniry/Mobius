//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StaticInitializationPO.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.proofobligation;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.statement.Statement;

/**
 * This class describes a proof obligation for a static initialization and 
 * facilities to calculate them.
 * @author L. Burdy
 **/
public class StaticInitializationPO extends SourceProofObligation {

	/**
	 * Constructs a proof obligation
	 * @param c The current class
	 * @param b The body
	 * @param p1 The normal behaviour proof
	 * @param p7 The exceptional behaviour proof
	 **/
	/*@
	  @ requires b != null;
	  @ requires c != null;
	  @*/
	public StaticInitializationPO(
		Class c,
		Statement b,
		Theorem p1,
		Theorem p7) {
		super(c.getBName() + "_Static_Initialisation", b, p1, p7, c, null);
	}

	/**
	 * Process the WP calculus on the proof obligations.
	 * Finalize the calculated lemmas.
	 **/
	public void pog(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		ExceptionalBehaviourStack ebs =
			new ExceptionalBehaviourStack(new ExceptionalProofs(getPhi7()));

		getCl().staticInitLemmas =
			getBody().ensures(
				config,
				getPhi1(),
				ebs,
				new Vector());
		getCl().staticInitLemmas.finalize(
			config,
			null,
			getCl().getStaticFinalFieldsInvariants((JavaLoader) config.getPackage()),
//			null,
			null,
			null,
			getName(),
			getBox(),
			new ColoredInfo());

	}

	public void proveObvious(boolean prove) {
		getCl().staticInitLemmas.proveObvious(prove, true);
	}

	public String getDisplayedName() {
		return "static intialization";
	}

}
