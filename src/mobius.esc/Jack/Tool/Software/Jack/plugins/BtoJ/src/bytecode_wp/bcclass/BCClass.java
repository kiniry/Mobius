/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass;

import jack.util.Logger;

import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.structure.IClass;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;

import bytecode_to_JPO.B2JPackage;
import bytecode_wp.bc.io.AttributeReader;
import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.attributes.BCAttribute;
import bytecode_wp.bcclass.attributes.ClassInvariant;
import bytecode_wp.bcclass.attributes.HistoryConstraints;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcclass.attributes.SecondConstantPool;
import bytecode_wp.bcclass.utils.MethodSignature;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bytecode.block.IllegalLoopException;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.vcg.VCGPath;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCClass implements IClass {
	private HashMap methods;

	private BCField[] fields;

	private String className;

	private String[] interfaceNames;

	private String superClassName;

	private BCConstantPool constantPool;
	
	private BCClass superClass;

	private HashMap interfaces;

	private String packageName;

	private HistoryConstraints historyConstraints;

	private ClassInvariant classInvariant;

	private ClassStateVector visibleState;

	public BCClass(JavaClass _clazz) throws ReadAttributeException {
		className = _clazz.getClassName();
		superClassName = _clazz.getSuperclassName();
		interfaceNames = _clazz.getInterfaceNames();
		packageName = _clazz.getPackageName();
		ConstantPoolGen cpg = new ConstantPoolGen(_clazz.getConstantPool());
		constantPool = new BCConstantPool(cpg);
		Attribute[] attributes = _clazz.getAttributes();
		setAttributes(cpg.getConstantPool(), attributes);
		Method[] methods = _clazz.getMethods();
		initMethods(methods, cpg);

		Field[] f = _clazz.getFields();
		initFields(f);
	}

	public void setConfig(IJml2bConfiguration config) {
		constantPool.setConfig(config);
	}

	public void getModifiesCondition(IJml2bConfiguration config, int state,
			ModifiesSet modifSet, VCGPath vcg) {
		if (visibleState == null) {
			initStateVector(config, null);
		}
		visibleState.atState(config, state, modifSet, vcg);
		/*
		 * if (f == null) { return Predicate0Ar.TRUE; } return f;
		 */
	}

	public Vector getInvariantsOfFields() {
		return null;
	}

	/**
	 * initialises the state vector
	 * 
	 * @param classesVisited
	 * @return
	 */
	public ClassStateVector initStateVector(IJml2bConfiguration config,
			Vector classesVisited) {
		if (visibleState == null) {
			visibleState = new ClassStateVector(this);
			visibleState.initStateVector(config, classesVisited,
					getPackageName());
		}
		return visibleState;
	}

	private void initFields(Field[] _fields) {
		if (_fields == null) {
			return;
		}
		fields = new BCField[_fields.length];
		for (int i = 0; i < _fields.length; i++) {
			fields[i] = new BCField(_fields[i]);

		}
	}

	private void setAttributes(ConstantPool cp, Attribute[] _attributes)
			throws ReadAttributeException {
		Unknown privateAttr = null;
		for (int i = 0; i < _attributes.length; i++) {
			if (_attributes[i] instanceof Unknown) {
				privateAttr = (Unknown) _attributes[i];
				BCAttribute bcAttribute = AttributeReader.readAttribute(
						privateAttr, this, null,
						new BCLocalVariable[] { new BCLocalVariable(0) });
				if (bcAttribute instanceof SecondConstantPool) 
					constantPool.add(cp,(SecondConstantPool) bcAttribute);
				if (bcAttribute instanceof ClassInvariant) {
					classInvariant = (ClassInvariant) bcAttribute;
				} else if (bcAttribute instanceof HistoryConstraints) {
					historyConstraints = (HistoryConstraints) bcAttribute;
				}
			}
		}
	}

	// sets the super class of this class
	public BCClass getSuperClass(IJml2bConfiguration config) {
		if (superClass != null) {
			return superClass;
		}
		superClass = ((B2JPackage) config.getPackage())
				.getClass(superClassName);
		return superClass;
	}



	// sets the interfaces implemented by this class
	private void setInterfaces(IJml2bConfiguration config) {
		if (interfaceNames == null) {
			return;
		}
		if (interfaces != null) {
			return;
		}
		interfaces = new HashMap();
		for (int i = 0; i < interfaceNames.length; i++) {
			BCClass _interface = ((B2JPackage) config.getPackage())
					.getClass(interfaceNames[i]);
			interfaces.put(interfaceNames[i], _interface);
		}
	}

	/**
	 * @return an object that represents constant pool of the class
	 */
	public BCConstantPool getConstantPool() {
		return constantPool;
	}

	/**
	 * NB : if a method with this signature is not found then may be an
	 * exception must be thrown
	 * 
	 * @param signature
	 * @return
	 * @throws ReadAttributeException
	 * @throws IllegalLoopException
	 */
	public BCMethod lookupMethod(IJml2bConfiguration config, String signature)
			throws ReadAttributeException, IllegalLoopException {
		BCMethod m = null;
		/*
		 * Util.dump("search for method " + signature + " in class " + className );
		 * Util.dumpMethods(this);
		 */
		m = (BCMethod) methods.get(signature);
		if (m != null) {
			m.initMethod();
			return m;
		}
		BCClass superClass = getSuperClass(config);
		m = superClass.lookupMethod(config, signature);
		if (m != null) {
			return m;
		}
		BCClass interfaze;
		for (int i = 0; i < interfaceNames.length; i++) {
			interfaze = ((B2JPackage) config.getPackage())
					.getClass(interfaceNames[i]);
			m = (BCMethod) interfaze.lookupMethod(config, signature);
			if (m != null) {
				return m;
			}
		}
		m.initMethod();
		return m;
	}

	/**
	 * searches for a field with name
	 * 
	 * @param fName
	 * @return
	 * @throws ReadAttributeException
	 * @throws IllegalLoopException
	 */
	public BCField lookupField(IJml2bConfiguration config, String fName)
			throws ReadAttributeException, IllegalLoopException {
		BCField f = null;
		/*
		 * Util.dump("search for method " + signature + " in class " + className );
		 * Util.dumpMethods(this);
		 */
		if (fields != null) {
			for (int i = 0; i < fields.length; i++) {
				if (fields[i].getName().equals(fName)) {
					return fields[i];
				}
			}
		}
		/*
		 * Util.dump("search for method " + signature + " in superclass " +
		 * superClassName );
		 */BCClass superClass = getSuperClass(config);
		f = superClass.lookupField(config, fName);
		if (f != null) {
			return f;
		}
		BCClass interfaze;
		for (int i = 0; i < interfaceNames.length; i++) {
			interfaze = ((B2JPackage) config.getPackage())
					.getClass(interfaceNames[i]);
			f = interfaze.lookupField(config, fName);
			if (f != null) {
				return f;
			}
		}
		return f;
	}

	/**
	 * initialises the methods that are declared in this class
	 * 
	 * @param methods
	 */
	private void initMethods(Method[] _methods, ConstantPoolGen cp)
			throws ReadAttributeException {
		methods = new HashMap();
		// for (int i = 0; i < _methods.length; i++) {
		for (int i = 0; i < _methods.length; i++) {
			MethodGen mg = new MethodGen(_methods[i], className, cp);
			BCMethod bcm = new BCMethod(mg, this, cp);
			//String signature = mg.getSignature();
			String key = MethodSignature.getSignature(bcm.getName(), bcm
					.getArgTypes(), bcm.getReturnType());
			/* Util.dump(" add method " + key + " in class " + getName() ); */
			methods.put(key, bcm);
		}
	}

	public String getName() {
		return className;
	}

	public void wp(IJml2bConfiguration config) throws ReadAttributeException,
			IllegalLoopException {
		Iterator miter = methods.values().iterator();
		setConfig(config);
		while (miter.hasNext()) {
			BCMethod m = (BCMethod) miter.next();
			Logger.out.println("wp for Method " + m.getName());
			m.initMethod();
			m.wp(config);

		}
	}

	
	
	public Collection getMethodKeys() {
		return methods.keySet();
	}

	/**
	 * @return Returns the methods.
	 */
	public Collection getMethods() {
		return methods.values();
	}

	/**
	 * @return Returns the classInvariant.
	 */
	public ClassInvariant getClassInvariant() {
		if (classInvariant == null) {
			return null;
		}
		return classInvariant;
	}

	/*	*//**
			 * @return Returns the classInvariant.
			 */
	/*
	 * public Formula getClassInvariantAfterConstructor() { if (classInvariant ==
	 * null) { return Predicate0Ar.TRUE; } return
	 * classInvariant.getClassInvariantAfterInit(); }
	 */

	/**
	 * @return Returns the historyConstraints.
	 */
	public Formula getHistoryConstraints() {
		if (historyConstraints == null) {
			return Predicate0Ar.TRUE;
		}
		return historyConstraints.getPredicate();
	}

	/**
	 * @return Returns the fields.
	 */
	public BCField[] getFields() {
		return fields;
	}

	public String toString() {
		return getName();
	}

	/**
	 * @param pt
	 */
	public void saveCode(PrintStream pt) {
		// TODO Auto-generated method stub

	}

	public String getBName() {
		return className;
	}

	public String getPackageName() {
		return packageName;
	}

}
