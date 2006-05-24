//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubArrayElementSingle
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class corresponds to the substitution of <code>xxxelements</code> with a 
 * <code>xxxelements <+ {f |-> xxxelements(f) <+ {i |-> v}}</code>.
 * @author L. Burdy
 **/
public class SubArrayElementSingle extends Profiler implements Substitution {

	/**
	 * The <code>xxxelements</code> variable that is modified.
	 **/
	private ElementsForm elements;

	/**
	* The formula that corresponds to the array
	**/
	private Formula array;

	/**
		* The formula that corresponds to the indice
		**/
	private Formula indice;

	/**
	  * The formula that corresponds to the new value
	  **/
	private Formula value;

	/*@
	  @ private invariant elements != null
	  @                && newElem != null;
	  @*/

	/**
	 * Constructs a substitution
	 * @param e The <code>xxxelements</code> variable
	 * @param n The new formula
	 **/
	/*@
	  @ requires e != null && n != null;
	  @*/
	public SubArrayElementSingle(
		ElementsForm e,
		Formula a,
		Formula i,
		Formula v) {
		elements = e;
		array = a;
		indice = i;
		value = v;
	}

	public Object clone() {
		return new SubArrayElementSingle(
			elements,
			(Formula) array.clone(),
			(Formula) indice.clone(),
			(Formula) value.clone());
	}

	public Formula sub(Formula f) {
		return f.subIdent(
			elements.getNonAmbiguousName(),
			new BinaryForm(
				B_OVERRIDING,
				elements,
				new BinaryForm(
					B_COUPLE,
					array,
					new BinaryForm(
						B_OVERRIDING,
						new BinaryForm(
							IFormToken.B_APPLICATION,
							elements,
							(Formula) array.clone()),
						new BinaryForm(B_COUPLE, indice, value)))));
	}

	public void sub(Substitution s) {
		array = s.sub(array);
		indice = s.sub(indice);
		value = s.sub(value);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(ARRAY_ELEMENT_SINGLE);
		array.save(config, s, jf);
		indice.save(config, s, jf);
		value.save(config, s, jf);
	}

}
