/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package annot.bcclass.attributes;

import annot.bcclass.BCMethod;
import annot.bcclass.BMLConfig;
import annot.formula.Formula;

/**
 * @author io
 * 
 *   
 */
public class Assert extends BCPrintableAttribute {
	

	// the position in the bytecode where the predicate must hold
//	private int pcIndex;
	
	private Formula assertFormula;
	public Assert(Formula _f, int _p, BCMethod m) {
			atype = "assert";
			assertFormula = _f;
			pcIndex = _p;
			method = m;
	}	
	
	/**
	 * 
	 * @return Returns the position where the predicate must hold
	 */
	public int getPosition() {
		return pcIndex;
	}
	
	/**
	 * @return
	 */
	public Formula getPredicate() {
		return assertFormula;
	}
	
	public String printCode (BMLConfig conf) {
		return conf.addComment("assert " + assertFormula.printLine(conf, 7));
	}

	@Override
	public void replaceWith(BCPrintableAttribute attr) {
		Assert[] at = method.getAssertTable().getAsserts();
		for (int i=0; i<at.length; i++)
			if (at[i] == this)
				at[i] = (Assert)attr;
	}
}
