//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubForm
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
 * This class corresponds to the substitution of a formula by another.
 * @author L. Burdy
 */
public class SubForm implements Substitution {

    /**
     * The old formula
     **/
	private Formula old;
	
    /**
     * The new formula
     **/
    private Formula newF;

    /*@
      @ private invariant old != null
      @                && newF != null;
      @*/

    /**
     * Constructs a substitution.
     * @param a The old formula
     * @param b The nex formula
     **/
	public SubForm(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
        throws IOException, jml2b.exceptions.LoadException {
		old = Formula.create(config, s, fi);
		newF = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.FORM);
		old.save(config, s, jf);
		newF.save(config, s, jf);
	}

    /**
     * @return old <- newF
     **/
	public String getInfo() {
		return old.toLangDefault(3) + " <- " + newF.toLangDefault(6);
	}

}
