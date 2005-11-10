/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;

import application.JavaApplication;
import bc.io.AttributeReader;
import bc.io.ReadAttributeException;
import bcclass.attributes.BCAttribute;
import bcclass.attributes.ClassInvariant;
import bcclass.attributes.HistoryConstraints;
import bcclass.attributes.ModifiesSet;
import bcclass.utils.MethodSignature;
import bytecode.block.IllegalLoopException;
import formula.Formula;
import formula.atomic.Predicate0Ar;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCClass {
	private HashMap methods;
	private BCField[] fields;

	private String className;

	private String[] interfaceNames;
	private String superClassName;

	private BCConstantPool constantPool;

	private BCClass superClass;

	private HashMap interfaces;

	private HistoryConstraints historyConstraints;
	private ClassInvariant classInvariant;
	private ClassStateVector stateVector;

	public BCClass(JavaClass _clazz) throws ReadAttributeException {
		className = _clazz.getClassName();
		superClassName = _clazz.getSuperclassName();
		interfaceNames = _clazz.getInterfaceNames();
		ConstantPoolGen cpg = new ConstantPoolGen(_clazz.getConstantPool());
		constantPool = new BCConstantPool(cpg);
		Attribute[] attributes = _clazz.getAttributes();
		setAttributes(attributes);
		Method[] methods = _clazz.getMethods();
		initMethods(methods, cpg);
		
		Field[] f = _clazz.getFields();
		initFields(f);
	}
	
/*	public Formula getVectorAtState(int state) {
		if (stateVector == null ) {
			initStateVector(null);
		}
		Formula f = stateVector.atState(state);
		return f;
	}*/
	
	public Formula getVectorAtStateToHold(int state, ModifiesSet modifSet) {
		if (stateVector == null ) {
			initStateVector(null);
		}
		Formula f = stateVector.atState(state, modifSet);
		if (f == null) {
			return Predicate0Ar.TRUE;
		}
		return f;
	}
	
	/**
	 * initialises the state vector
	 * @param classesVisited
	 * @return
	 */
	public ClassStateVector initStateVector( Vector classesVisited) {
		if ( stateVector == null) {
			stateVector = new ClassStateVector(this);
			stateVector.initStateVector(classesVisited);
		}
		return stateVector;
	}
 	
	private void initFields( Field[] _fields ) {
		if ( _fields == null ) {
			return;
		}
		fields = new BCField[_fields.length];
		for (int i = 0; i < _fields.length; i++) {
			fields[i] = new BCField(_fields[i]);
			
		}
	}

	private void setAttributes(Attribute[] _attributes)
		throws ReadAttributeException {
		Unknown privateAttr = null;
		for (int i = 0; i < _attributes.length; i++) {
			if (_attributes[i] instanceof Unknown) {
				privateAttr = (Unknown) _attributes[i];
				BCAttribute bcAttribute =
					AttributeReader.readAttribute(privateAttr, constantPool, null, null);
				if (bcAttribute instanceof ClassInvariant) {
					classInvariant = (ClassInvariant) bcAttribute;
				} else if (bcAttribute instanceof HistoryConstraints) {
					historyConstraints = (HistoryConstraints) bcAttribute;
				}
			}
		}
	}

	//sets the super class of this class
	public BCClass getSuperClass() {
		if (superClass != null) {
			return superClass;
		}
		superClass = JavaApplication.Application.getClass(superClassName);
		return superClass;
	}

	//sets the interfaces implemented by this class
	private void setInterfaces() {
		if (interfaceNames == null) {
			return;
		}
		if (interfaces != null) {
			return;
		}
		interfaces = new HashMap();
		for (int i = 0; i < interfaceNames.length; i++) {
			BCClass _interface =
				JavaApplication.Application.getClass(interfaceNames[i]);
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
	 * NB :  if a method with this signature is not found then may be an exception must be thrown 
	 * @param signature
	 * @return
	 * @throws ReadAttributeException
	 * @throws IllegalLoopException
	 */
	public BCMethod lookupMethod(String signature) throws ReadAttributeException, IllegalLoopException {
		BCMethod m = null;
		/*Util.dump("search for method " + signature + "   in class "  + className );
		Util.dumpMethods(this);*/
		m = (BCMethod) methods.get(signature);
		if (m != null) {
			m.initMethod();
			return m;
		}
	/*	Util.dump("search for method " + signature + "            in superclass "  + superClassName );
*/		BCClass superClass = getSuperClass();
		m = superClass.lookupMethod(signature);
		if (m != null) {
			
			return m;
		}
		BCClass interfaze;
		for (int i = 0; i < interfaceNames.length; i++) {
			interfaze = JavaApplication.Application.getClass(interfaceNames[i]);
			m = (BCMethod) interfaze.lookupMethod(signature);
			if (m != null) {
				return m;
			}
		}
		m.initMethod();
		return m;
	}

	/**
	 * initialises the methods that are declared in this class
	 * @param methods
	 */
	private void initMethods(Method[] _methods, ConstantPoolGen cp)
		throws ReadAttributeException {
		methods = new HashMap();
		//	for (int i = 0; i < _methods.length; i++)  {
		for (int i = 0; i < _methods.length ;i++) {
			MethodGen mg = new MethodGen(_methods[i], className, cp);
			BCMethod bcm = new BCMethod(mg,  this, cp);
			String signature = mg.getSignature();	
			String key = MethodSignature.getSignature(bcm.getName(), bcm.getArgTypes(), bcm.getReturnType());
			/*Util.dump(" add method " + key + " in class " + getName() );*/
			methods.put(key,bcm);
		}
	}

	public String getName() {
		return className;
	}

	public void wp() throws ReadAttributeException, IllegalLoopException {
		Iterator miter = methods.values().iterator();
		while (miter.hasNext()) {
			BCMethod m = (BCMethod) miter.next();
			m.initMethod();
			m.wp();
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
	public Formula getClassInvariant() {
		if (classInvariant == null) {
			return Predicate0Ar.TRUE;
		}
		return classInvariant.getClassInvariant();
	}
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
	
	
}
