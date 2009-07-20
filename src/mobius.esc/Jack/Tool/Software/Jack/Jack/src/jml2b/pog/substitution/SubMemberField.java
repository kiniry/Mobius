//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubMemberField
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TerminalForm;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class implements a substitution of a member field <code>a</code> by 
 * <code>a <+ { b |-> c }</code> corresponding to an affectation of a new value
 * for a given instance.
 * @author L. Burdy
 */
public class SubMemberField extends Profiler implements Substitution {

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
    /*@
      @ requires a != null && b != null && c != null && d != null;
      @*/
	public SubMemberField(Formula a, String b, String c, Formula d) {
		old = a;
		this.b = new TerminalForm(b);
		this.c = new TerminalForm(c);
		this.d = d;
	}

	/**
	 * Constructs a substitution form another one or from a loaded one
	 * @param a The initial member field
	 * @param b The new member field
	 * @param c The instance
	 * @param d The value
	 **/
    /*@
      @ requires a != null && b != null && c != null && d != null;
      @*/
	public SubMemberField(Formula a, Formula b, Formula c, Formula d) {
		old = a;
		this.b = b;
		this.c = c;
		this.d = d;
	}

	public Object clone() {
		return new SubMemberField(
			old,
			(Formula) b.clone(),
			(Formula) c.clone(),
			(Formula) d.clone());
	}

	/**
	 * @return [old := b <+ {c |->d}]f
	 **/
	public Formula sub(Formula f) {
		return f.sub(
			old,
			new BinaryForm(B_OVERRIDING, b, new BinaryForm(B_COUPLE, c, d)),
			false);
	}

	public void sub(Substitution s) {
		b = s.sub(b);
		c = s.sub(c);
		d = s.sub(d);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(MEMBER_FIELD);
		old.save(config, s, jf);
		b.save(config, s, jf);
		c.save(config, s, jf);
		d.save(config, s, jf);
	}

	public Formula getField() {
		return old;
	}

	public Formula getInstance() {
		return c;
	}

}
