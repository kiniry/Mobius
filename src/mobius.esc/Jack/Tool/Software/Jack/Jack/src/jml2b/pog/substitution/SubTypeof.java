//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTypeof
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
 * This abstract class describes substitutions applied on <code>typeof</code>
 * @author L. Burdy
 */
public abstract class SubTypeof extends Profiler implements Substitution {

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
     * Constructs a substitution for <code>typeof</code>
     * @param f The formula corresponding to the extended typeof domain
     * @param t The formula corresponding to the value asociated to new domain
     **/
    /*@
      @ requires f != null && t != null;
      @*/
    public SubTypeof(Formula f, Formula t) {
        this.f = f;
        this.t = t;
    }

    abstract public Object clone();
    
    public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
        f.save(config, s, jf);
        t.save(config, s, jf);
    }

    public void sub(Substitution s)  {
        f = s.sub(f);
    }
    
	/**
	 * Returns the formula corresponding to the extended typeof domain.
	 * @return <code>f</code>
	 */
	public Formula getF() {
		return f;
	}

	/**
	 * Returns the formula corresponding to the value asociated to new domain.
	 * @return <code>t</code>
	 */
	public Formula getT() {
		return t;
	}

}
