/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.ref;



import type.BCType;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Reference extends Expression {
	
	private JavaType type;
	private int id;
	
	public Reference(int _id, JavaType _type) {
		id = _id;
		type = _type;
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
	public BCType getType()  {
		return type;
	}
}
