/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import type.BCType;
import bcclass.BCLocalVariable;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ObjectAccess extends Expression implements ReferenceExpression {
	private BCLocalVariable local;
	private int local_index;
	
	public ObjectAccess(BCLocalVariable _local) {
		local = _local;
		//setExpressionType(ExpressionConstants.OBJECTACCESS);
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
}
