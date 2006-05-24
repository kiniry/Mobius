//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTmpVar
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
 * This class corresponds to the substitution of a tempory variable with a 
 * formula.
 * @author L. Burdy
 **/
public class SubTmpVar extends Profiler implements Substitution {

	/**
	 * The temporary variable
	 **/
	private String tmp;

	/**
	 * The new formula
	 **/
	private Formula f;

    /*@
      @ private invariant tmp != null && f != null;
      @*/

	/**
	 * Constructs a substitution.
	 * @param tmp The temporary variable
	 * @param f The new formula
	 **/
    /*@
      @ requires tmp != null && f != null;
      @*/
	public SubTmpVar(String tmp, Formula f) {
		this.tmp = tmp;
		this.f = f;
	}

	public Object clone() {
		return new SubTmpVar(tmp, (Formula) f.clone());
	}

	public Formula sub(Formula p) {
		return p.subIdent(tmp, f);
	}

	public void sub(Substitution s) {
		f = s.sub(f);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(TMP_VAR);
		s.writeUTF(tmp);
		f.save(config, s, jf);
	}

}
