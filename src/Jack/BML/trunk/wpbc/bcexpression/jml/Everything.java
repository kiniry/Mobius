/*
 * Created on Sep 2, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.jml;

import type.BCType;
import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * this class stands for the jml keyword everything used in the clause modifies in the method specification.
 *  if a method is declared to modify everything it is considered  that every field of the class that it belongs to, every public field of any class
 * of the same package and 
 *
 */
public class Everything  extends JMLExpression {
	
	public static Everything EVERYTHING = new  Everything(); 


	private Everything() {
	}
	
	
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		// TODO Auto-generated method stub
		return "\\everything";
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return null;
	}
	

}
