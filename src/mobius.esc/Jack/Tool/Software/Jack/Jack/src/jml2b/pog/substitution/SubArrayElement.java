//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubArrayElement
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
 * This class corresponds to the substitution of <code>xxxelements</code> with a 
 * formula.
 * @author L. Burdy
 **/
public class SubArrayElement extends Profiler implements Substitution {

    /**
     * The <code>xxxelements</code> variable that is modified.
     **/
	private String elements;
    
    /**
     * The formula that corresponds to the new value
     **/
	private Formula newElem;

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
	public SubArrayElement(String e, Formula n) {
		elements = e;
		newElem = n;
	}

	public Object clone() {
		return new SubArrayElement(elements, (Formula) newElem.clone());
	}

	public Formula sub(Formula f)  {
		return f.subIdent(elements, newElem);
	}

	public void sub(Substitution s)  {
		newElem = s.sub(newElem);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(ARRAY_ELEMENT);
		s.writeUTF(elements);
		newElem.save(config, s, jf);
	}

}
