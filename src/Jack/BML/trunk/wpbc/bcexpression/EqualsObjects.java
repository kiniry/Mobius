/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import type.BCType;
/**
 * @deprecated
 * @author mpavlova
 * 
 * this class represents an expression that is out of the Java language. It
 * models references . Example (a  WITH r := s)(o) is desugared to : if o == r
 * then s else a(o)
 */
public class EqualsObjects extends Expression {
	/**
	 * represents the field the WITH reference
	 */
	private Expression with;
//	/**
//	 * represents the field that is tested if it is equal to the reference
//	 * alias
//	 */
//	private Expression objReference;
	
	/**
	 * substitute with this object if with == objReference
	 */
	private Expression substituteWith;
	
/*	public WITH(Expression _with) {
		objReference = null;
		with = _with;
	}
	*/
	/*public WITH(Expression _objReference, Expression _alias, Expression _substituteWith) {
		objReference = _objReference;
		with = _alias;
		substituteWith = _substituteWith;
	}*/
	
	public EqualsObjects( Expression _with, Expression _substituteWith) {
		//objReference = _objReference;
		with = _with;
		substituteWith = _substituteWith;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
//	/**
//	 * @return Returns the objReference.
//	 */
//	public Expression getObjReference() {
//		return objReference;
//	}


	/**
	 * @return Returns the with.
	 */
	public Expression getWith() {
		return with;
	}
	
	/**
	 * substitute in both expressions 
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		with  = with.substitute(_e1, _e2);
		substituteWith = substituteWith.substitute(_e1, _e2);
		
		//substituteWith = substituteWith.substitute(_e1, _e2);
		return this;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = with.toString() + "<---" +substituteWith.toString();
		return s;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		// TODO Auto-generated method stub
		return null;
	}
}
