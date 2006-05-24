//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;
import jml2b.structure.statement.UnaryExp;

/**
 * @author L. Burdy
 */
public class VariantLemma
	extends SimpleLemma
	implements JmlDeclParserTokenTypes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public VariantLemma(IJml2bConfiguration config, Expression f)
		throws Jml2bException, PogException {

		super(
			config,
			Expression.and(
				new BinaryExp(
					RELATIONAL_OP,
					f,
					">=",
					new TerminalExp(NUM_INT, "0")),
				new BinaryExp(
					RELATIONAL_OP,
					f,
					"<",
					new UnaryExp(MyToken.T_VARIANT_OLD, "OLD", f))),
			new GoalOrigin(GoalOrigin.LOOP_VARIANT));
	}

}
