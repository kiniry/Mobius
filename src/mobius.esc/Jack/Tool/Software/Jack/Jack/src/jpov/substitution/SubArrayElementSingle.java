//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubArrayElement
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
 * This class corresponds to the substitution of <code>xxxelements</code> with a 
 * formula.
 * @author L. Burdy
 */
public class SubArrayElementSingle implements Substitution {

	/**
	 * The formula that corresponds to the new value
	 **/
	private Formula array;
	
	private Formula indice;
	
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
	public SubArrayElementSingle(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		array = Formula.create(config, s, fi);
		indice = Formula.create(config, s, fi);
		value = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.ARRAY_ELEMENT_SINGLE);
		array.save(config, s, jf);
		indice.save(config, s, jf);
		value.save(config, s, jf);
	}

    /**
     * @return elements <- newElem
     **/
	public String getInfo() {
		return array.toLangDefault(0) + "[" + indice.toLangDefault(0) + "] <- " + value.toLangDefault(3);
	}

}
