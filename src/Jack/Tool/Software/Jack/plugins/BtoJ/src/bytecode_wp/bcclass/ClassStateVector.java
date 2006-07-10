/*
 * Created on 27 sept. 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcclass;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import bytecode_to_JPO.B2JPackage;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.StaticFieldAccess;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.constants.BCConstantClass;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.utils.FreshIntGenerator;
import bytecode_wp.vcg.VCGPath;
import bytecode_wp.vcg.VcType;

/**
 * @author io
 * 
 * these are the locations that are visible in the class -i.e. the fields of the
 * imported classes and those that are in the same package
 */
public class ClassStateVector {
	private Vector stateVector;

	private BCClass clazz;

	public static final int RETURN_STATE = -1;

	public ClassStateVector(BCClass _clazz) {
		clazz = _clazz;
	}

	/**
	 * generates a vector of locations that may be modified in the class. These
	 * are the classes that are imported in the class and also the classes that
	 * are in the same package
	 * 
	 * @param classesVisited
	 * @param _package
	 *            TODO
	 * 
	 * @return
	 */
	public Vector initStateVector(IJml2bConfiguration config,
			Vector classesVisited, String _package) {
		if (stateVector != null) {
			return stateVector;
		}
		if (classesVisited == null) {
			classesVisited = new Vector();
		}
		classesVisited.add(clazz);
		BCConstantPool pool = clazz.getConstantPool();
		pool.setConfig(config);
		stateVector = new Vector();
		BCField[] fields = clazz.getFields();
		if (fields != null) {
			for (int i = 0; i < fields.length; i++) {
				if (fields[i].isVisible()) {
					continue;
				}
				String name = fields[i].getName();
				/* JavaType type = fields[i].getType(); */
				BCConstantFieldRef fieldRef = null;
				// searches if the field is dereferenced
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
						/*
						 * JavaType constType = (JavaType) constField.getType();
						 * if (type != constType) { continue; }
						 */
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

		// take into account the classes that are visible from this class
		for (int i = 1; i < pool.getSize(); i++) {
			if (pool.getConstant(i) instanceof BCConstantClass) {
				BCConstantClass constClass = (BCConstantClass) pool
						.getConstant(i);
				String className = constClass.getName();
				if (clazz.getName().equals(className)) {
					continue;
				}
				// if the constant class describes an array then do not inspect
				// it
				if (className.startsWith("[")) {
					continue;
				}
				BCClass c = ((B2JPackage) config.getPackage())
						.getClass(className);
				if (!c.getPackageName().equals(_package)) {
					continue;
				}
				Vector v = c.initStateVector(config, classesVisited)
						.getVector();
				stateVector.addAll(v);
			}
		}

		/*
		 * stateVector = new Vector(); Enumeration classes = ((B2JPackage)
		 * config.getPackage()) .getClasses().elements();
		 * 
		 * while (classes.hasMoreElements()) { BCClass clazz =
		 * (BCClass)classes.nextElement(); BCConstantPool pool =
		 * clazz.getConstantPool(); BCField[] fields = clazz.getFields(); if
		 * (fields != null) { for (int i = 0; i < fields.length; i++) { if
		 * (!fields[i].isVisible()) { continue; } String name =
		 * fields[i].getName(); JavaType type = fields[i].getType();
		 * BCConstantFieldRef fieldRef = null; // searches if the field is
		 * dereferenced for (int n = 1; n < pool.getSize(); n++) { // searches
		 * if this field is dereferenced in the class if (pool.getConstant(n)
		 * instanceof BCConstantFieldRef) { BCConstantFieldRef constField =
		 * (BCConstantFieldRef) pool .getConstant(n); BCConstantClass
		 * constFieldDeclaredInClass = (BCConstantClass) pool
		 * .getConstant(constField.getClassIndex()); if
		 * (!(constFieldDeclaredInClass.getName().equals(clazz .getName()))) {
		 * continue; } if (type != (JavaType) constField.getType()) { continue; }
		 * if (!name.equals(constField.getName())) { continue; } fieldRef =
		 * constField; break; } } if (fieldRef != null) {
		 * stateVector.add(fieldRef); } } } }
		 */
		return stateVector;
	}

	public Vector getVector() {
		return stateVector;
	}

	public void atState(IJml2bConfiguration config, int state,
			ModifiesSet modSet, VCGPath vcg) {

		if (modSet.modifiesEverything()) {
			return;
		}
		modSet.getPostcondition(config, state, vcg);

		for (int i = 0; i < stateVector.size(); i++) {
			BCConstantFieldRef fieldRef = (BCConstantFieldRef) stateVector
					.elementAt(i);
			if ((!modSet.modifiesNothing()) && (modSet.modifies(fieldRef))) {
				continue;
			}
			Formula forAllfAtStateEqf = getFieldAtState(state, fieldRef);
			vcg.addGoal(VcType.MODIFIES, forAllfAtStateEqf);
			/* f = Formula.getFormula(f, forAllfAtStateEqf, Connector.AND); */
		}
		/*
		 * // deprecated f = Formula.getFormula(f, modifiesAtState,
		 * Connector.AND);
		 */
	}

	private Formula getFieldAtState(int state, BCConstantFieldRef fieldRef) {
		if (fieldRef.isStatic()) {
			return getStaticFieldInState(state, fieldRef);
		} else {
			return getInstanceFieldInState(state, fieldRef);
		}
	}

	private Formula getInstanceFieldInState(int state,
			BCConstantFieldRef fieldRef) {
		Variable objDeref = new Variable(FreshIntGenerator.getInt(), fieldRef
				.getClassWhereDeclared());
		// typeof(o) <: typeof (fieldRef)
		Predicate2Ar domainObjDeref = new Predicate2Ar(new TYPEOF(objDeref),
				fieldRef.getClassWhereDeclared(), PredicateSymbol.SUBTYPE);

		FieldAccess fAcc = new FieldAccess(fieldRef, objDeref);
		Predicate2Ar fAtStateEqf;
		if (state == RETURN_STATE) {
			fAtStateEqf = new Predicate2Ar(fAcc, new OLD(fAcc.copy()),
					PredicateSymbol.EQ);
		} else {
			fAtStateEqf = new Predicate2Ar(fAcc, fAcc.copy().atState(state,
					fAcc.getSubExpressions()[0]), PredicateSymbol.EQ);
		}
		Formula forAllfAtStateEqf = Formula.getFormula(Formula.getFormula(
				domainObjDeref, fAtStateEqf, Connector.IMPLIES),
				new Quantificator(Quantificator.FORALL, objDeref));
		return forAllfAtStateEqf;
	}

	private Formula getStaticFieldInState(int state, BCConstantFieldRef fieldRef) {
		/*
		 * Variable objDeref = new Variable(FreshIntGenerator.getInt(),
		 * fieldRef.getClassWhereDeclared()); // typeof(o) <: typeof (fieldRef)
		 * Predicate2Ar domainObjDeref = new Predicate2Ar(new TYPEOF(objDeref),
		 * fieldRef.getClassWhereDeclared(), PredicateSymbol.SUBTYPE);
		 */

		BCConstantClass clazz = fieldRef.getConstantClass();
		StaticFieldAccess fAcc = new StaticFieldAccess(fieldRef, clazz);
		Predicate2Ar fAtStateEqf = null;
		if (state == RETURN_STATE) {
			fAtStateEqf = new Predicate2Ar(fAcc, new OLD(fAcc.copy()),
					PredicateSymbol.EQ);
		} else {
			fAtStateEqf = new Predicate2Ar(fAcc, fAcc.copy().atState(state,
					fAcc.getSubExpressions()[0]), PredicateSymbol.EQ);
		}
		/*
		 * Formula forAllfAtStateEqf = Formula.getFormula(Formula.getFormula(
		 * domainObjDeref, fAtStateEqf, Connector.IMPLIES), new
		 * Quantificator(Quantificator.FORALL, objDeref));
		 */
		return fAtStateEqf;
	}

}
