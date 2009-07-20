//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.proofobligation;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.Invariant;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.Statement;

/**
 * @author L. Burdy
 */
public class WellDefinedInvPO extends SourceProofObligation {

	private static Expression toExpression(Enumeration invariants) {
		Expression res = Expression.getTrue();
		while (invariants.hasMoreElements()) {
			Invariant i = (Invariant) invariants.nextElement();
			res = Expression.and(res, i.getInvariant());
		}
		return res;
	}

	public WellDefinedInvPO(
		IJml2bConfiguration config,
		Class c,
		Enumeration invariants)
		throws Jml2bException, PogException {
		super(
			"Invariant_well_definedness",
			(Statement) toExpression(invariants),
			null,
			null,
			c,
			new ColoredInfo());
	}

	public void pog(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		getCl().wellDefInvLemmas =
			getBody().ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector());

		getCl().wellDefInvLemmas.finalize(
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
		getCl().wellDefInvLemmas.proveObvious(prove, true);

	}

	public String getDisplayedName() {
		return "checking well definedness";
	}

}
