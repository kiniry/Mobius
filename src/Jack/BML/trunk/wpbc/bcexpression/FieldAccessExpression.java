/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import constants.BCConstant;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class FieldAccessExpression  extends  CPExpression {

	/**
	 * @param _right
	 * @param _left
	 * @param _type
	 */
	public FieldAccessExpression(BCConstant _right, Expression _left) {
		super(_right, _left);
		
	}
	
}
