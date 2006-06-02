//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /* Created on Oct 5, 2004
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import jml2b.formula.Formula;
import jml2b.pog.lemma.VirtualFormula;

/**
 *
 *  @author L. Burdy
 **/
public class B2JVirtualFormula extends VirtualFormula {

	/** */
	private static final long serialVersionUID = 1L;
	Formula formula;
	/**
	 * @param decl
	 */
	public B2JVirtualFormula(Formula decl) {
		formula = decl;
	}

	public Formula getFormula() {
		return formula;
	}
}
