/*
 * Created on May 13, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.substitution;

import javax.swing.text.html.ObjectView;

import utils.Util;

import bcexpression.Expression;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class SubstitutionUnit  implements Tree {
	private  Expression  object;
	private  Expression  value;
	
	public SubstitutionUnit( Expression _object, Expression _value) {
		object = _object;
		value = _value;
	}
	
	
	public Expression getObject( ) { 
		return object;
	}
	
	public Expression getValue( ) { 
			return value;
	}

	/* (non-Javadoc)
	 * @see bcexpression.objectsubstitution.Tree#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Tree substitute(Expression e1, Expression e2)  {
//		Util.dump("SubstitutionUnit.substitute ****************** " + toString() + "[" +e1 + "<--"+ e2 + "]");
//		Util.dump("SubstitutionUnit  object before " + object.toString() );
		object = object.substitute(e1, e2);
//		Util.dump("SubstitutionUnit  object after " + object.toString() );
//		Util.dump("SubstitutionUnit  value before " + value.toString() );
		value = value.substitute( e1, e2);
//		Util.dump("SubstitutionUnit  value after " + value.toString() );
		return this;
	}
	
	public String toString() {
		String s = "( " + object.toString() + " <- " + value.toString() + " )";
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.substitution.Tree#copy()
	 */
	public Tree copy() {
		Expression objectCopy = object.copy();
		Expression valueCopy = value.copy();
		SubstitutionUnit unitCopy = new SubstitutionUnit( objectCopy, valueCopy) ;
		return unitCopy;
	}
	
}
