package annot.bcclass.attributes;

import annot.bcclass.BCClass;
import annot.bcclass.BMLConfig;
import annot.modifexpression.Everything;
import annot.modifexpression.ModifiesExpression;

//import jml2b.IJml2bConfiguration;
//import annot.bcclass.BCClass;
//import annot.bcclass.BCConstantPool;
//import bytecode_wp.bcexpression.BCLocalVariable;
//import bytecode_wp.bcexpression.Expression;
//import annot.constants.BCConstantFieldRef;
//import annot.formula.Formula;
//import annot.formula.Predicate0Ar;
//import annot.modifexpression.Everything;
//import annot.modifexpression.ModifiesExpression;
//import annot.modifexpression.ModifiesLocalVariable;
//import annot.modifexpression.Nothing;
//import bytecode_wp.vcg.VCGPath;
//import bytecode_wp.vcg.VcType;

public class ModifiesSet implements BCAttribute {
	private ModifiesExpression[] modifiesExpression;
	private BCClass clazz;
	
	public ModifiesSet(ModifiesExpression[] _modifiesExpression, BCClass _clazz ) {
		modifiesExpression = _modifiesExpression;
		clazz = _clazz;
	}
	
	public String printCode(BMLConfig conf, int usedc) {
		if (modifiesExpression.length <= 0)
			return "?";
		String code = "";
		conf.incInd();
		for (int i=0; i<modifiesExpression.length; i++)
			if (modifiesExpression[i] != null) {
//				if (i > 0)
//					code += ", ";
				code += conf.expr_block_start + modifiesExpression[i].printCode(conf);
				if (i < modifiesExpression.length - 1)
					code += ", ";
				code += conf.expr_block_end;
			}
		code = conf.pp.breakLines(code, usedc);
		conf.decInd();
		return code;
	}
	
	public ModifiesExpression[] getModifiesExpressions() {
		return modifiesExpression;
	}
	 
//	public Formula getPostcondition(IJml2bConfiguration config, int state, VCGPath vcg) {
//		Formula modPost = Predicate0Ar.TRUE;
//		if (modifiesExpression == null ) {
//			return modPost;
//		}
//		for (int i = 0; i < modifiesExpression.length; i++) {
//			if (modifiesExpression[i] == null) {
//				continue;
//			}
//			if (modifiesExpression[i] instanceof ModifiesLocalVariable) {
//				continue;
//			}
//			Formula f = (Formula)modifiesExpression[i].getPostCondition(config, state);
//			vcg.addGoal( VcType.MODIFIES, f);
//			
//			if ( f == null) {
//				continue;
//			}
//			//modPost = Formula.getFormula(modPost, f, Connector.AND);
//		}
//		return modPost;
//	}
//	
//	public Expression[] getExpressions() {
//		Expression[] expressions;
//		if (modifiesExpression == null ) {
//			return null;
//		}
//		expressions = new Expression[modifiesExpression.length ];
//		for (int i = 0; i < modifiesExpression.length; i++) {
//			if (modifiesExpression[i] == null) {
//				continue;
//			}
//			Expression e = modifiesExpression[i].getExpression();
//			expressions[i] = e; 
//		}
//		return expressions;
//	}
//	
//	public boolean modifiesNothing() {
//		if (modifiesExpression[0] == Nothing.NOTHING) {
//			return true;
//		}
//		return false;
//	}
//	
//	public boolean modifiesEverything() {
//		if (modifiesExpression[0] instanceof Everything) {
//			return true;
//		}
//		return false;
//	}
//	
//	/**
//	 * 
//	 * looks if the fieldRef is modified by this modifies set
//	 * @param fieldRef 
//	 * @return
//	 */
//	public boolean modifies(BCConstantFieldRef fieldRef) {
//		
//		 
//		for (int k = 0; k < modifiesExpression.length; k++ ) {
//			if (modifiesExpression[k] == null) {
//				continue;
//			} 
//			BCConstantFieldRef modConstFieldRef = (BCConstantFieldRef)modifiesExpression[k].getExpressionModifies() ;
//			// if there is  a modifies expression that modifies this field then return true 
//			if ( modConstFieldRef == fieldRef) {
//				return true;
//			}					
//		}
//		return false;
//	}
//	
//	/**
//	 * @param fieldRef
//	 * @return
//	 */
//	public boolean modifies(BCLocalVariable locVar) {
//		 
//		for (int k = 0; k < modifiesExpression.length; k++ ) {
//			if (modifiesExpression[k] == null) {
//				continue;
//			} 
//			if ( !(modifiesExpression[k] instanceof ModifiesLocalVariable) ) {
//				continue;
//			}
//			ModifiesLocalVariable modLocVar = (ModifiesLocalVariable)modifiesExpression[k];
//			// if there is  a modifies expression that modifies this local variable then return true 
//			if ( locVar.equals( modLocVar.getLocalVariable()) ) {
//				return true;
//			}					
//		}
//		return false;
//	}
//	
//	/**
//	 * @return Returns the constantPool.
//	 */
//	public BCConstantPool getConstantPool() {
//		return clazz.getConstantPool();
//	}
}
