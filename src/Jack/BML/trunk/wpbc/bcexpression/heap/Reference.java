/*
 * Created on 16 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.heap;



import bcexpression.Expression;
import bcexpression.type.JavaType;

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
}
