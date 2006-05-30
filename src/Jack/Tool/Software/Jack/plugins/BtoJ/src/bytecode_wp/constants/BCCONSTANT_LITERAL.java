/*
 * Created on Apr 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.constants;

import bytecode_wp.bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class BCCONSTANT_LITERAL extends BCConstant { 
	
	public BCCONSTANT_LITERAL(int _cp_index) {
		super(_cp_index);
	}
	
	public abstract Expression getLiteral();
}
