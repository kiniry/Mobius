/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.vm;



import type.BCType;
import bcexpression.ArithmeticExpression;
import bcexpression.Expression;
import bcexpression.Variable;
import bcexpression.javatype.JavaBasicType;
import bcexpression.javatype.JavaType;



/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Counter  extends Expression {
	
	
	public Counter() {
		
	}


	

	private final JavaBasicType type = JavaType.JavaINT ; 


	/* *
	 * the type of the stack counter is int by default, that's why this method inherited from the super abstarct class Expression 
	 * doesn't do anything 
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
	}


	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	
	
}
