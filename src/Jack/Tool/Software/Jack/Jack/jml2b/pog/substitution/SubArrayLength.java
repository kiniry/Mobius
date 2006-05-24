//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubArrayLength
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
 * This class corresponds to the substitution of <code>arraylength</code> with a 
 * formula.
 * @author L. Burdy
 **/
public class SubArrayLength extends Profiler implements Substitution {

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
    /*@
      @ requires f != null;
      @*/
	public SubArrayLength(Formula f) {
		this.f = f;
	}
    
    public Object clone() {
        return new SubArrayLength((Formula) f.clone());
    }

	public Formula sub(Formula p)  {
		return p.subIdent("arraylength", f);
	}

	public void sub(Substitution s)  {
		f = s.sub(f);
	}

    public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
        s.writeByte(ARRAY_LENGTH);
        f.save(config, s, jf);
    }

}
