/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package annot.bcexpression.jml;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcexpression.javatype.JavaType;



/**
 * @author io
 *
 * this class represents the JML constant type : 
 */
public class _TYPE extends JMLExpression  {
	
	//jml expression : type( expression) where expression is a java type 
	public _TYPE(JavaType _type) {
		super(_type);
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return JML_CONST_TYPE.JML_CONST_TYPE;
	} 
	
//	public   boolean equals(Expression _expr){ 
//		if ( _expr == this) {
//			return true;
//		}
//		return false;
//		
//	}
//	public Expression substitute(Expression _e1 , Expression _e2) { 
//		return this;
//	}
//
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#toString()
//	 */
	public String printCode(BMLConfig conf) {
		return "\type(" + getType() + ")";
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
	
		return this;
	}
}
