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

import jml2b.formula.Formula;
import jml2b.pog.lemma.NonObviousGoal;


/**
 *
 *  @author L. Burdy
 **/
public class B2JNonObviousGoal extends NonObviousGoal {

	Formula goal;
	/**
	 * @param formula
	 */
	public B2JNonObviousGoal(Formula formula) {
		goal = formula;
	}
	public jml2b.formula.Formula getFormula() {
		return goal;
	}
}
