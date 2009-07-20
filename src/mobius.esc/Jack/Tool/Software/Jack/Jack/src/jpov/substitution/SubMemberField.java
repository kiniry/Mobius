//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubMemberField
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
 * This class implements a substitution of a member field <code>a</code> by 
 * <code>a <+ { b |-> c }</code> corresponding to an affectation of a new value
 * for a given instance.
 * @author L. Burdy
 */
public class SubMemberField implements Substitution {

    /**
     * The initial member field
     **/
	private Formula old;

    /**
     * The new member field
     **/
	private Formula b;
    
    /**
     * The instance that is modified
     **/
	private Formula c;
    
    /**
     * The value assign to the field for this instance
     **/
	private Formula d;

    /*@
      @ private invariant old != null
      @                && b != null
      @                && c != null
      @                && d != null;
      @*/

    /**
     * Constructs a substitution
     * @param a The initial member field
     * @param b The new member field
     * @param c The instance
     * @param d The value
     **/
	public SubMemberField(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
        throws IOException, jml2b.exceptions.LoadException {
		old = Formula.create(config, s, fi);
		b = Formula.create(config, s, fi);
		c = Formula.create(config, s, fi);
		d = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.MEMBER_FIELD);
		old.save(config, s, jf);
		b.save(config, s, jf);
		c.save(config, s, jf);
		d.save(config, s, jf);
	}

	public String getInfo() {
         return c.toLangDefault(3) + "." + old.toLangDefault(6) + " <- " + d.toLangDefault(9);
	}

}
