/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.overload;

import java.util.Vector;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class OverloadList {
	/*private Tree left;
	private Tree right;*/
	
	private Vector overloads;
	
	public OverloadList(Expression expr1, Expression expr2) {
		OverloadEqUnit unit = new OverloadEqUnit(expr1, expr2);
		overloads = new Vector();
		overloads.add( unit);
		/*setLeft(left);*/
	}

	public OverloadList() {
		
	}
	
	public OverloadList(Vector _overloads) {
			overloads = _overloads;
	}
	
	public void overload(OverloadUnit unit) {
		if (overloads == null) {
			overloads = new Vector();
		}
		overloads.add( unit);
	}
	
	
	protected Expression getExpressionOverloading( Expression expr) {
		if (overloads == null) {
			return null;
		}
		for (int i = 0; i < overloads.size() ; i++) {
			OverloadUnit unit = (OverloadUnit)( overloads.get(i));
			Expression overloading = unit.getExpressionOverloading(expr );
			if (overloading != null) {
				return overloading;
			}
		}
		return null;
	}
	
/*	*//**
	 * deprecated
	 * @param left
	 * @param right
	 *//*
	public OverloadList(Overload left, Overload right) {
		setLeft(left);
		setRight(right);
	}*/

	public OverloadList substitute(Expression e1, Expression e2) {
		if ( overloads == null) {
			return this;
		} 
		
		for (int i = 0; i < overloads.size() ; i++) {
			OverloadUnit unit = (OverloadUnit)( overloads.get(i));
			unit = (OverloadUnit)unit.copy();
		}
		return this;
	}

	/**
	 * @param tree
	 *//*
	public void setLeft(Tree tree) {
		left = tree;
	}*/

	/**
	 * @param tree
	 *//*
	public void setRight(Tree tree) {
		right = tree;
	}*/

	public String toString() {
		String s = "";
		
		for (int i = 0; i < overloads.size() ; i++) {
			OverloadUnit unit = (OverloadUnit)( overloads.get(i));
			s  =  s + " " +  unit.toString();	
		}
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.substitution.Tree#copy()
	 */
	public OverloadList copy() {
		if ( overloads == null) {
			System.out.println("Warning : a null list of overloads ");
			return null;
		} 
		OverloadList overLoadCopy = new OverloadList();
		for (int i = 0; i < overloads.size() ; i++) {
			OverloadUnit unit = (OverloadUnit)( overloads.get(i));
			unit = (OverloadUnit ) unit.copy();
			overLoadCopy.overload(unit);
		}
		return overLoadCopy;
	}

}
