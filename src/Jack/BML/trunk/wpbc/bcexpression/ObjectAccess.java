/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import bcclass.BCLocalVariable;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ObjectAccess extends Expression {
	BCLocalVariable local;
	
	public ObjectAccess(BCLocalVariable _local) {
		local = _local;
		//setExpressionType(ExpressionConstants.OBJECTACCESS);
	}
	
	//LB A quoi serve ces operations qui retournent null ?
	public Object getLeft() {
		return null;
	}
	
	public Object getRight() {
		return null;
	}
	
	public Expression getObject() {
		return this;
	}
}
