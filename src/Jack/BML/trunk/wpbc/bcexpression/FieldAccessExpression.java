/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import type.BCType;
import constants.BCConstant;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class FieldAccessExpression  extends  DOTExpression {

	/**
	 * @param _right
	 * @param _left
	 * @param _type
	 */
	public FieldAccessExpression(BCConstant _left, Expression _right) {
		super( _left , _right);
		
	}
	
	public FieldAccessExpression(Expression _left, Expression _right)  { 
		super(_left, _right);
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return  getLeft().getType();
	}
	
}
