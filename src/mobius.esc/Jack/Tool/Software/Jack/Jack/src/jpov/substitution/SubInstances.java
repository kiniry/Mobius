//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubInstances
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class corresponds to the substitution of <code>instances</code> with:
 * <UL>
 * <li> <code>instances \/ f</code>
 * <li> <code>instances \/ {f}</code>
 * </UL>
 * @author L. Burdy
 */
abstract class SubInstances implements Substitution {

	/**
	 * The formula used to substitute <code>instances</code>
	 **/
	private Formula f;

	/*@
	  @ private invariant f != null;
	  @*/

	/**
	 * Constructs a substitution for <code>instances</code>
	 * @param f The formula
	 **/
	SubInstances(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		f = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		f.save(config, s, jf);
	}

	/**
	 * Returns the formula.
	 * @return <code>f</code>
	 */
	final Formula getF() {
		return f;
	}

}
