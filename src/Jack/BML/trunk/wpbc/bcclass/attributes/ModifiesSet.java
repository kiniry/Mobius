/*
 * Created on 21 sept. 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;

import utils.FreshIntGenerator;
import constants.BCConstantClass;
import constants.BCConstantFieldRef;
import bcclass.BCConstantPool;
import bcexpression.Expression;
import bcexpression.FieldAccess;
import bcexpression.Variable;
import bcexpression.javatype.JavaType;
import bcexpression.jml.OLD;
import bcexpression.jml.TYPEOF;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.atomic.Predicate;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;
import modifexpression.Everything;
import modifexpression.ModifiesExpression;
import modifexpression.Nothing;

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
	 
	public Formula getPostcondition( ) {
		Formula modPost = Predicate.TRUE;
		if (modifiesExpression == null ) {
			return modPost;
		}
		for (int i = 0; i < modifiesExpression.length; i++) {
			if (modifiesExpression[i] == null) {
				continue;
			}
			Formula f = (Formula)modifiesExpression[i].getPostCondition();
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
	
	public Formula getConditionForNonModifiedFields( /*ModifiesExpression[] modifiesExpressions*/ ) {
		
		Formula noModifCondition = Predicate.TRUE;
		if (modifiesExpression[0] == Nothing.NOTHING ) {
			// then make for every constant field in the constant pool a formula that states
			// that the field is not modified
			
			for (int i = 1; i< constantPool.getSize() ; i++ ) {		
				if (constantPool.getConstant(i) instanceof BCConstantFieldRef ) {
					BCConstantFieldRef constField = (BCConstantFieldRef)constantPool.getConstant(i);
					BCConstantClass bcConstantClass = (BCConstantClass)constantPool.getConstant( constField.getClassIndex() ); 
					JavaType type = JavaType.getJavaType(bcConstantClass.getName());
					Variable var = new Variable(FreshIntGenerator.getInt());
					 
					FieldAccess fAccess = new FieldAccess( constField,  var);
					Predicate2Ar fAccessRqOldfAccess = new  Predicate2Ar(fAccess, new OLD(fAccess), PredicateSymbol.EQ );
					Quantificator quantif = new Quantificator(Quantificator.FORALL, var, new Predicate2Ar( new TYPEOF( var), type , PredicateSymbol.SUBTYPE) );
					Formula f = Formula.getFormula( fAccessRqOldfAccess, quantif);
					noModifCondition = Formula.getFormula( noModifCondition, f, Connector.AND);
				}
			}
			return noModifCondition;
		}
		if (modifiesExpression[0] == Everything.EVERYTHING) {
			// then it can change anything it wants so
			// do nothing here butq when method is called quantify over ebery possible cionstant
			// field application
			return noModifCondition;
		} 
		
		for (int i = 1; i< constantPool.getSize() ; i++ ) {		
			if (constantPool.getConstant(i) instanceof BCConstantFieldRef ) {
				BCConstantFieldRef constField = (BCConstantFieldRef)constantPool.getConstant(i);
				int k;
				for (k = 0; k < modifiesExpression.length; k++ ) {
					BCConstantFieldRef modConstFieldRef = (BCConstantFieldRef)modifiesExpression[k].getConstantFieldRef() ;
					// if there is  an expression over this field then do nothing for this field
					if ( modConstFieldRef == constField) {
						break;
					}					
				}
				//in case this field is not said to be modified then state that it's not changed by the method
				if ( k == modifiesExpression.length) {
					 BCConstantClass bcConstantClass = (BCConstantClass)constantPool.getConstant( constField.getClassIndex()); 
					 JavaType type = JavaType.getJavaType(bcConstantClass.getName());
					 Variable var = new Variable(FreshIntGenerator.getInt());
					 
					 FieldAccess fAccess = new FieldAccess( constField,  var);
					 Predicate2Ar fAccessRqOldfAccess = new  Predicate2Ar(fAccess, new OLD(fAccess), PredicateSymbol.EQ );
					 Quantificator quantif = new Quantificator(Quantificator.FORALL, var, new Predicate2Ar( new TYPEOF( var), type, PredicateSymbol.SUBTYPE ) );
					 Formula f = Formula.getFormula( fAccessRqOldfAccess, quantif);
					 noModifCondition = Formula.getFormula( noModifCondition, f, Connector.AND);
				}	
			}
			
		}
		/////////////////////// then the same for all the references in the cosntant pool that are not
		////////// should not be modified by the method
		return noModifCondition;
	}
	
	
	public ModifiesSet copy() {
		ModifiesExpression[] modExprCopy = new ModifiesExpression[modifiesExpression.length];
		for (int i = 0 ; i < modifiesExpression.length; i++) {
			modExprCopy[i] = (ModifiesExpression)modifiesExpression[i].copy();
		}
		ModifiesSet copy = new ModifiesSet( modExprCopy, constantPool);
		return copy;
	}
	
	
	
}
