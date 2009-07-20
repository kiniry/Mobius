//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubForm
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
 * This class corresponds to the substitution of a formula by another.
 * @author L. Burdy
 **/
public class SubForm extends Profiler implements Substitution {

    /**
     * The old formula
     **/
	protected Formula old;
    
    /**
     * The new formula
     **/
	protected Formula newF;

    /*@
      @ private invariant old != null
      @                && newF != null;
      @*/
    
    /**
     * Constructs a substitution.
     * @param a The old formula
     * @param b The nex formula
     **/
    /*@
      @ requires a != null && b != null;
      @*/
	public SubForm(Formula a, Formula b) {
		old = a;
		newF = b;
	}

	public Object clone() {
		return new SubForm(old, (Formula) newF.clone());
	}

	public Formula sub(Formula f)   {
		return f.sub(old, newF, false);
	}

	public void sub(Substitution s) {
		newF = s.sub(newF);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(FORM);
		old.save(config, s, jf);
		newF.save(config, s, jf);
	}

}
