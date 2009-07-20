//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubArrayLength
/*
/*******************************************************************************
/* Warnings/Remarks:
//*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class corresponds to the substitution of <code>arraylength</code> with a 
 * formula.
 * @author L. Burdy
 **/
public class SubArrayLength implements Substitution {

	/**
	 * The formula that is substitute to  <code>arraylength</code>
	 **/
	private Formula f;

	/*@
	  @ private invariant f != null;
	  @*/

	/**
	 * Constructs a substitution
	 * @param f The formula to substitute to  <code>arraylength</code>
	 **/
	public SubArrayLength(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		f = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.ARRAY_LENGTH);
		f.save(config, s, jf);
	}

	/**
	 * Returns "arraylength == f"
	 **/
	public String getInfo() {
		return "arraylength <- " + f.toLangDefault(3);
	}

}
