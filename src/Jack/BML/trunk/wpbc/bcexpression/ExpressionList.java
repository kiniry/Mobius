/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */

/**
 * this class is used to represent a list exressions - mainly for the case when
 * method calls with arguments is done 
 * 
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ExpressionList extends Expression {
	private Expression[]  el;
	
	public ExpressionList(Expression[] _el) {
		el = _el;
	}
}
