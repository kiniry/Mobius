/*
 * Created on 27 sept. 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass;
import java.util.Vector;

import modifexpression.ModifiesExpression;

import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.util.ClassVector;

import utils.FreshIntGenerator;
import constants.BCConstantClass;
import constants.BCConstantFieldRef;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;

import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;
import application.JavaApplication;
import bcclass.attributes.ModifiesSet;
import bcexpression.FieldAccess;
import bcexpression.Variable;
import bcexpression.javatype.JavaReferenceType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.OLD;
import bcexpression.jml.TYPEOF;
/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public class ClassStateVector {
	private Vector stateVector;
	private BCClass clazz;
	
	public static final int RETURN_STATE = -1;
	
	public ClassStateVector(BCClass _clazz) {
		clazz = _clazz;
	}
	
	public Vector initStateVector(Vector classesVisited) {
		if (stateVector != null) {
			return stateVector;
		}
		if (classesVisited == null) {
			classesVisited = new Vector();
		}
		classesVisited.add(clazz);
		
		BCConstantPool pool = clazz.getConstantPool();
		stateVector = new Vector();
		BCField[] fields = clazz.getFields();
		if (fields != null) {
			for (int i = 0; i < fields.length; i++) {
				if (!fields[i].isVisible()) {
					continue;
				}
				String name = fields[i].getName();
				JavaType type = fields[i].getType();
				BCConstantFieldRef fieldRef = null;
				for (int n = 1; n < pool.getSize(); n++) {
					if (pool.getConstant(n) instanceof BCConstantFieldRef) {
						BCConstantFieldRef constField = (BCConstantFieldRef) pool
								.getConstant(n);
						BCConstantClass constFieldDeclaredInClass = (BCConstantClass) pool
								.getConstant(constField.getClassIndex());
						if (!(constFieldDeclaredInClass.getName().equals(clazz
								.getName()))) {
							continue;
						}
						if (type != (JavaType) constField.getType()) {
							continue;
						}
						if (!name.equals(constField.getName())) {
							continue;
						}
						fieldRef = constField;
						break;
					}
				}
				if (fieldRef != null) {
					stateVector.add(fieldRef);
				}
			}
		}
		for (int i = 1; i < pool.getSize(); i++) {
			if (pool.getConstant(i) instanceof BCConstantClass) {
				BCConstantClass constClass = (BCConstantClass) pool
						.getConstant(i);
				String className = constClass.getName();
				//if the constant class describes an array then do not inspect it
				if (className.startsWith("[")) {
					continue;
				}
				BCClass c = JavaApplication.Application.getClass(className);
				
				if ( (!c.getName().startsWith("bcclass.")) || (classesVisited.contains(c))) {
					continue;
				}
				
				Vector v = c.initStateVector(classesVisited).getVector();
				stateVector.addAll(v);
			}
		}
		return stateVector;
	}
	
	
	
	public Vector getVector(){
		return stateVector;
	}
		
	
	public Formula atState(int state, ModifiesSet modSet) {
		Formula f = Predicate0Ar.TRUE;
		
		if (modSet.modifiesEverything()) {
			return Predicate0Ar.TRUE;
		}
		//deprecated
		/*Formula modifiesAtState = modSet.getPostcondition(state);*/
		/*if (state == ClassStateVector.RETURN_STATE) {
			return modifiesAtState;
		}*/
		for (int i = 0 ; i < stateVector.size() ; i++) {
			BCConstantFieldRef fieldRef = (BCConstantFieldRef) stateVector.elementAt(i);		
			if ( (!modSet.modifiesNothing() ) && ( modSet.modifies( fieldRef) )) {
				continue;
			}
			Formula forAllfAtStateEqf = getFieldAtState( state, fieldRef);
			f = Formula.getFormula(f, forAllfAtStateEqf, Connector.AND );
		}
		//deprecated
		/*f = Formula.getFormula(f, modifiesAtState, Connector.AND);*/
		return f;
	}
	
	
	private Formula getFieldAtState(int state, BCConstantFieldRef fieldRef ) {
		Variable objDeref =  new Variable(FreshIntGenerator.getInt(), JavaReferenceType.ReferenceType );
		// typeof(o) <: typeof (fieldRef)
		Predicate2Ar domainObjDeref = new Predicate2Ar(new TYPEOF(objDeref) , fieldRef.getType(), PredicateSymbol.SUBTYPE);
		
		FieldAccess fAcc = new FieldAccess(fieldRef, objDeref );
		Predicate2Ar fAtStateEqf ;
		if (state == RETURN_STATE ) {
			fAtStateEqf = new Predicate2Ar(  fAcc, new OLD(fAcc.copy()) , PredicateSymbol.EQ);
		} else {
			fAtStateEqf = new Predicate2Ar(  fAcc, fAcc.copy().atState(state) , PredicateSymbol.EQ);
		}
		Formula forAllfAtStateEqf = Formula.getFormula(Formula.getFormula(domainObjDeref, fAtStateEqf  , Connector.IMPLIES ),  new Quantificator(Quantificator.FORALL, objDeref));
		return forAllfAtStateEqf;
		
	}
	
	
 }
