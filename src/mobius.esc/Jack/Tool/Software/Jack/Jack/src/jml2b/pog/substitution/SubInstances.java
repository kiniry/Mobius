//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubInstances
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class corresponds to the substitution of <code>instances</code> with:
 * <UL>
 * <li> <code>instances \/ f</code>
 * <li> <code>instances \/ {f}</code>
 * </UL>
 * @author L. Burdy
 */
public abstract class SubInstances extends Profiler implements Substitution {

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
    /*@
      @ requires f != null;
      @*/
	SubInstances(Formula f) {
		this.f = f;
	}

	abstract public Object clone();

	public void sub(Substitution s) {
		f = s.sub(f);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		f.save(config, s, jf);
	}

	/**
	 * Returns the formula used to substitute <code>instances</code>
	 * @return <code>f</code>
	 */
	final Formula getF() {
		return f;
	}

}
