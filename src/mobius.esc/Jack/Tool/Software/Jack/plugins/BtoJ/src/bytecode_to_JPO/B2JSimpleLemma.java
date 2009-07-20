//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /* Created on Sep 29, 2004
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.pog.lemma.SimpleLemma;


/**
 *
 *  @author L. Burdy
 **/
public class B2JSimpleLemma extends SimpleLemma {

	/** */
	private static final long serialVersionUID = 1L;
	Vector goals;
	
	/**
	 * @param formula
	 */
	public B2JSimpleLemma(IJml2bConfiguration config, Vector goals) throws Jml2bException{
		this.goals = new Vector();
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			bytecode_wp.formula.Formula f = (bytecode_wp.formula.Formula) e.nextElement();
			this.goals.add(new B2JNonObviousGoal(B2JProofs.toFormula(config, f, new HashSet())));
		}
	}
	
	public Enumeration getGoals() {
		return goals.elements();
	}

}
