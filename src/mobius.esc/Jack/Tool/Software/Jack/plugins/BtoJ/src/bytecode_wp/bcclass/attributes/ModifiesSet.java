/*
 * Created on 21 sept. 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcclass.attributes;

import jml2b.IJml2bConfiguration;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.modifexpression.Everything;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesLocalVariable;
import bytecode_wp.modifexpression.Nothing;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ModifiesSet implements BCAttribute {
	private ModifiesExpression[] modifiesExpression;
	private BCClass clazz;
	
	public ModifiesSet(ModifiesExpression[] _modifiesExpression, BCClass _clazz ) {
		modifiesExpression = _modifiesExpression;
		clazz = _clazz;
	}
	
	public ModifiesExpression[] getModifiesExpressions() {
		return modifiesExpression;
	}
	 
	public Formula getPostcondition(IJml2bConfiguration config, int state, VCGPath vcg) {
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
			Formula f = (Formula)modifiesExpression[i].getPostCondition(config, state);
			vcg.addGoal( VcType.MODIFIES, f);
			
			if ( f == null) {
				continue;
			}
			//modPost = Formula.getFormula(modPost, f, Connector.AND);
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
		if (modifiesExpression[0] instanceof Everything) {
			return true;
		}
		return false;
	}
	
	/**
	 * 
	 * looks if the fieldRef is modified by this modifies set
	 * @param fieldRef 
	 * @return
	 */
	public boolean modifies(BCConstantFieldRef fieldRef) {
		
		 
		for (int k = 0; k < modifiesExpression.length; k++ ) {
			if (modifiesExpression[k] == null) {
				continue;
			} 
			BCConstantFieldRef modConstFieldRef = (BCConstantFieldRef)modifiesExpression[k].getExpressionModifies() ;
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
		return clazz.getConstantPool();
	}
}
