/*
 * Created on 21 sept. 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;

import modifexpression.Everything;
import modifexpression.ModifiesExpression;
import modifexpression.ModifiesLocalVariable;
import modifexpression.Nothing;

import constants.BCConstantFieldRef;
import bcclass.BCConstantPool;
import bcexpression.BCLocalVariable;
import bcexpression.Expression;

import formula.Connector;
import formula.Formula;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ModifiesSet implements BCAttribute {
	private ModifiesExpression[] modifiesExpression;
	private BCConstantPool constantPool;
	 
	public ModifiesSet(ModifiesExpression[] _modifiesExpression, BCConstantPool _constantPool ) {
		modifiesExpression = _modifiesExpression;
		constantPool = _constantPool;
	}
	
	public ModifiesExpression[] getModifiesExpressions() {
		return modifiesExpression;
	}
	 
	public Formula getPostcondition( int state) {
		Formula modPost = Predicate0Ar.TRUE;
		if (modifiesExpression == null ) {
			return modPost;
		}
		for (int i = 0; i < modifiesExpression.length; i++) {
			if (modifiesExpression[i] == null) {
				continue;
			}
			if (modifiesExpression[i] instanceof ModifiesLocalVariable) {
				continue;
			}
			Formula f = (Formula)modifiesExpression[i].getPostCondition(state);
			if ( f == null) {
				continue;
			}
			modPost = Formula.getFormula(modPost, f, Connector.AND);
		}
		return modPost;
	}
	
	public Expression[] getExpressions() {
		Expression[] expressions;
		if (modifiesExpression == null ) {
			return null;
		}
		expressions = new Expression[modifiesExpression.length ];
		for (int i = 0; i < modifiesExpression.length; i++) {
			if (modifiesExpression[i] == null) {
				continue;
			}
			Expression e = modifiesExpression[i].getExpression();
			expressions[i] = e; 
		}
		return expressions;
	}
	
	public boolean modifiesNothing() {
		if (modifiesExpression[0] == Nothing.NOTHING) {
			return true;
		}
		return false;
	}
	
	public boolean modifiesEverything() {
		if (modifiesExpression[0] == Everything.EVERYTHING) {
			return true;
		}
		return false;
	}
	
	/**
	 * @param fieldRef
	 * @return
	 */
	public boolean modifies(BCConstantFieldRef fieldRef) {
		
		if (modifiesExpression == null) 
		for (int k = 0; k < modifiesExpression.length; k++ ) {
			if (modifiesExpression[k] == null) {
				continue;
			} 
			BCConstantFieldRef modConstFieldRef = (BCConstantFieldRef)modifiesExpression[k].getConstantFieldRef() ;
			// if there is  a modifies expression that modifies this field then return true 
			if ( modConstFieldRef == fieldRef) {
				return true;
			}					
		}
		return false;
	}
	
	/**
	 * @param fieldRef
	 * @return
	 */
	public boolean modifies(BCLocalVariable locVar) {
		 
		for (int k = 0; k < modifiesExpression.length; k++ ) {
			if (modifiesExpression[k] == null) {
				continue;
			} 
			if ( !(modifiesExpression[k] instanceof ModifiesLocalVariable) ) {
				continue;
			}
			ModifiesLocalVariable modLocVar = (ModifiesLocalVariable)modifiesExpression[k];
			// if there is  a modifies expression that modifies this local variable then return true 
			if ( locVar.equals( modLocVar.getLocalVariable()) ) {
				return true;
			}					
		}
		return false;
	}
	
	
	
	
	
	/**
	 * @return Returns the constantPool.
	 */
	public BCConstantPool getConstantPool() {
		return constantPool;
	}
}
