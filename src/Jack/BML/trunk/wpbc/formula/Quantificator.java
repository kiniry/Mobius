/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package formula;

import java.util.Vector;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Quantificator {
	public static final String FORALL = "forall"; 
	public static final String  EXISTS = "exists";
	private Vector bound_vars;
	private String quantifier;
	
	public Quantificator(String _quantifier)  {
		quantifier = _quantifier;
	}
	
	public Quantificator(String  _quantifier, Vector _ids) {
		this(_quantifier);
		bound_vars = _ids;
	}
	
	public void addBoundVar(Vector var)  {
		if (bound_vars == null) {
			bound_vars = new Vector();
		}
		bound_vars.add(var);
	}
	
	public void dump() {
	
	}
}
