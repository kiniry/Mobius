//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: VirtualFormula.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.JmlFile;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class implements a formula with its set of colored informations.
 * @author L. Burdy
 */
public class VirtualFormula extends Profiler implements Serializable {

	/**
	 * Formula origin corresponding to a require clause
	 **/
	public final static byte REQUIRES = 0;

	/**
	 * Formula origin corresponding to a local hypothese
	 **/
	public final static byte LOCALES = 1;

	/**
	 * Formula origin corresponding to an assertion
	 **/
	public final static byte ASSERT = 2;

	/**
	 * Formula origin corresponding to an ensures clause of a called method
	 **/
	public final static byte ENSURES = 3;

	/**
	 * Formula origin corresponding to an exsures clause of a called method
	 **/
	public final static byte EXSURES = 4;

	/**
	 * Formula origin corresponding to a loop invariant
	 **/
	public final static byte LOOP_INVARIANT = 5;

	/**
	 * Formula origin corresponding to a loop exsures
	 **/
	public final static byte LOOP_EXSURES = 6;

	/**
	 * Formula origin corresponding to an ensures clause of a specified block
	 **/
	public final static byte BLOCK_ENSURES = 7;

	/**
	 * Formula origin corresponding to an exsures clause of a specified block
	 **/
	public final static byte BLOCK_EXSURES = 8;

	/**
	 * Formula origin corresponding to an invariant
	 **/
	public final static byte INVARIANT = 9;

	/**
	 * Formula origin corresponding to a static final field initialization
	 **/
	public final static byte STATIC_FINAL_FIELDS_INVARIANT = 10;

	/**
	 * Formula origin corresponding to a goal
	 **/
	public final static byte GOAL = 11;

	public final static byte PURE_METHOD_DECLARATION = 12;

	/**
	 * Returns the number of hypothese type
	 **/
	public static int getMaxHypType() {
		return 12;
	}

	/**
	 * Returns the string corresponding to an hypothesis type
	 * @param type The hypothesis type
	 * @return The string to display
	 **/
	public static String getHypTypeString(byte type) {
		switch (type) {
			case LOOP_EXSURES :
				return "Loop exsures";
			case LOCALES :
				return "Locales";
			case ENSURES :
				return "Ensures from called method";
			case EXSURES :
				return "Exsures from called method";
			case REQUIRES :
				return "Requires";
			case INVARIANT :
				return "Invariant";
			case STATIC_FINAL_FIELDS_INVARIANT :
				return "Invariant from static final fields";
			case LOOP_INVARIANT :
				return "Loop invariant";
			case ASSERT :
				return "Assertion";
			case BLOCK_ENSURES :
				return "Ensures from block";
			case BLOCK_EXSURES :
				return "Exsures from block";
			case PURE_METHOD_DECLARATION :
				return "Pure method exsures clause";
			default :
				return "";
		}
	}

	/**
	 * The formula
	 **/
	private Formula f;

	/**
	 * Set of colored informations associated with the formula
	 **/
	private Vector flow;

	/**
	 * Index of the formula (used to save the formula into jpo file)
	 **/
	private int index;

	/**
	 * The origin of the formula
	 **/
	private byte origin;

	/*@ 
	  @ private invariant f != null
	  @                && flow != null;
	  @*/

	public VirtualFormula() {
		
	}
	
	/**
	 * Constructs a virtual formula
	 * @param origin The origin
	 * @param f The formula
	 * @param b The associated colored information
	 **/
	/*@ 
	  @ requires f != null;
	  @*/
	public VirtualFormula(byte origin, Formula f, ColoredInfo b) {
		this.f = f;
		flow = new Vector();
		if (b != null)
			flow.add(b);
		this.origin = origin;
	}

	/**
	 * Constructs a virtual formula
	 * @param origin The origin
	 * @param f The formula
	 * @param b The associated set of colored informations
	 **/
	/*@
	  @ requires f != null && b != null;
	  @*/
	public VirtualFormula(byte origin, Formula f, Vector b) {
		this.f = f;
		flow = b;
		this.origin = origin;
	}

	/**
	 * Apply a substitution to the formula.
	 * @param s substitution to apply.
	 * @return the current formula substituted.
	 **/
	VirtualFormula sub(Substitution s) {
		Formula fo = s.sub(f);
		if (fo == f)
			return this;
		else
			return new VirtualFormula(origin, fo, flow);
	}

	/**
	 * Suppress the <i>Called Old</i> expressions in the formula.
	 * @return the current formula when the <i>Called Old</i> have been 
	 * suppressed.
	 **/
	VirtualFormula suppressSpecialOld(int token) {
		Formula fo = f.suppressSpecialOld(token);
		if (fo == f)
			return this;
		else
			return new VirtualFormula(origin, fo, flow);
	}

	/**
	 * Returns the formula
	 * @return <code>f</code>
	 **/
	//@ ensures \result != null;
	public Formula getFormula() {
		return f;
	}

	/**
	 * Returns the set of colored informations associated with the formula
	 * @return <code>flow</code>
	 **/
	//@ ensures \result != null;
	Vector getBox() {
		return flow;
	}

	/**
	 * Returns the index of the formula
	 * @return <code>index</code>
	 **/
	public int getIndex() {
		return index;
	}

	/**
	 * Saves the virtual formula into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The ouput stream corresponding to the jpo file
	 * @param index The index of the formula into the hypothesis array
	 * @param jf The current JML file
	 * @throws IOException
	 **/
	/*@
	  @ requires s != null;
	  @ modifies index;
	  @*/
	public void save(IJml2bConfiguration config, JpoOutputStream s, int index, JmlFile jf) throws IOException {
		this.index = index;
		s.writeInt(index);
		s.writeByte(origin);
		f.save(config, s, jf);
		s.writeInt(flow.size());
		Enumeration e = flow.elements();
		while (e.hasMoreElements()) {
			ColoredInfo element = (ColoredInfo) e.nextElement();
			element.save(s, 0, jf);
		}
	}

	void getFields(Set fields) {
		f.getFields(fields);
	}

	/**
	 * Annotates all the fields that appear in the formula to declare them in 
	 * the Atelier B files.
	 **/
	void garbageIdent() {
		f.garbageIdent();
	}

	/**
	 * Returns the origin.
	 * @return <code>origin</code>
	 */
	public byte getOrigin() {
		return origin;
	}

	/**
	 * Sets the origin.
	 * @param origin The origin to set
	 */
	public void setOrigin(byte origin) {
		this.origin = origin;
	}

	static final long serialVersionUID = 4922534264367790116L;

	/**
	 * 
	 */
	public boolean getsFlow(byte b) {
		boolean res = false;
		Enumeration e = flow.elements();
		while (e.hasMoreElements()) {
			ColoredInfo element = (ColoredInfo) e.nextElement();
			res = res || element.getComment() == b;
		}
		return res;
		
	}

}