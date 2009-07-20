//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTypeof.java
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
 * This abstract class describes substitutions applied on <code>typeof</code>
 * @author L. Burdy
 */
abstract class SubTypeof implements Substitution {

	/**
	 * The formula corresponding to the extended typeof domain
	 **/
	private Formula f;

	/**
	 * The formula corresponding to the value asociated to new domain
	 **/
	private Formula t;

	/*@
	  @ private invariant f != null
	  @                && t != null;
	  @*/

	/**
	 * Constructs a substitution from a loaded
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream 
	 **/
	SubTypeof(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		f = Formula.create(config, s, fi);
		t = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		f.save(config, s, jf);
		t.save(config, s, jf);
	}

	/**
	 * Returns the formula corresponding to the extended typeof domain.
	 * @return <code>f</code>
	 */
	final Formula getF() {
		return f;
	}

	/**
	 * Returns the formula corresponding to the value asociated to new domain.
	 * @return <code>t</code>
	 */
	final Formula getT() {
		return t;
	}

}
