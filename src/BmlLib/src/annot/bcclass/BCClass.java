package annot.bcclass;

import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;

import annot.bcclass.attributes.Assert;
import annot.bcclass.attributes.BCAttribute;
import annot.bcclass.attributes.BCPrintableAttribute;
import annot.bcclass.attributes.ClassInvariant;
import annot.bcclass.attributes.HistoryConstraints;
import annot.bcclass.attributes.LoopSpecification;
import annot.bcclass.attributes.SecondConstantPool;
import annot.bcclass.attributes.SingleLoopSpecification;
import annot.bcclass.parsing.Parsing;
import annot.bcclass.utils.MethodSignature;
import annot.bcexpression.BCLocalVariable;
import annot.bcio.AttributeReader;
import annot.bcio.ReadAttributeException;
import annot.bytecode.block.IllegalLoopException;

public class BCClass {
//	private HashMap<String, BCMethod> methods;
	public Vector<BCMethod> metody;
	private BCField[] fields;
	private String className;
	private String[] interfaceNames;
	private String superClassName;
	private BCConstantPool constantPool;
//	private BCClass superClass;
//	private HashMap interfaces;
	private String packageName;
	private HistoryConstraints historyConstraints;
	private ClassInvariant classInvariant;
//	private ClassStateVector visibleState;
	public Parsing parser;
	public boolean silent;

	public BCClass(JavaClass _clazz) throws ReadAttributeException {
		this(_clazz, false);
	}
	
	public BCClass(JavaClass _clazz, boolean s) throws ReadAttributeException {
		silent = s;
		AttributeReader.silent = s;
		parser = new Parsing(this);
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
		InicjalizujMetody();
	}

	public void InicjalizujMetody() throws ReadAttributeException {
		try {
			Iterator iter = metody.iterator();
			while (iter.hasNext()) {
				BCMethod m = (BCMethod)(iter.next());
				if (!silent)
					System.out.println("Initializing nethod: "+m.getName());
				m.initMethod();
			}
		} catch (Exception e) {
			e.printStackTrace();	// XXX: wywalic
			throw new ReadAttributeException("Bd przy inicjalizacji metod");
		}
	}
	
	public BCPrintableAttribute[] getAllAttributes() {
		Vector<BCPrintableAttribute> v = new Vector<BCPrintableAttribute>();
		Iterator iter = metody.iterator();
		while (iter.hasNext()) {
			BCMethod m = (BCMethod)(iter.next());
			v.add(m.getMethodSpecification());
			if (m.getAssertTable() != null) {
				Assert[] at = m.getAssertTable().getAsserts();
				for (int i=0; i<at.length; i++)
					v.add(at[i]);
			}
			if (m.getLoopSpecification() != null) {
				SingleLoopSpecification[] lt = m.getLoopSpecification().getLoopSpecifications();
				for (int i=0; i<lt.length; i++)
					v.add(lt[i]);
			}
		}
		BCPrintableAttribute[] arr = new BCPrintableAttribute[v.size()];
		v.copyInto(arr);
		String code = printCode();
		for (int i=0; i<code.split("\n").length; i++)
			parser.getAttributeAtLine(code, i);
		return arr;
	}
	
	public String printCode() {
		BMLConfig conf = new BMLConfig(constantPool);
		String code = "";
		if (!"".equals(packageName))
			code += "package " + packageName + "\n\n";
		code += "class " + className;
		if (!"java.lang.Object".equals(superClassName))
			code += " extends " + superClassName;
		if (interfaceNames.length > 0) {
			code += " implements ";
			for (int i=0; i<interfaceNames.length; i++)
				code += interfaceNames[i] + ((i < interfaceNames.length-1) ? ", " : "");
		}
		code += " {\n\n";
		Iterator iter = metody.iterator();
//		iter.next(); -- pominicie wypisywania inita.
		while (iter.hasNext())
			code += ((BCMethod)(iter.next())).printCode(conf) + "\n";
		code += "}\n";
		code = conf.pp.afterDisplay(code);
		return code;
	}
	
//	public void setConfig(IJml2bConfiguration config) {
//		constantPool.setConfig(config);
//	}
//
//	public void getModifiesCondition(IJml2bConfiguration config, int state,
//			ModifiesSet modifSet, VCGPath vcg) {
//		if (visibleState == null) {
//			initStateVector(config, null);
//		}
//		visibleState.atState(config, state, modifSet, vcg);
//		/*
//		 * if (f == null) { return Predicate0Ar.TRUE; } return f;
//		 */
//	}
//
//	public Vector getInvariantsOfFields() {
//		return null;
//	}
//
//	/**
//	 * initialises the state vector
//	 * 
//	 * @param classesVisited
//	 * @return
//	 */
//	public ClassStateVector initStateVector(IJml2bConfiguration config,
//			Vector classesVisited) {
//		if (visibleState == null) {
//			visibleState = new ClassStateVector(this);
//			visibleState.initStateVector(config, classesVisited,
//					getPackageName());
//		}
//		return visibleState;
//	}

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
						privateAttr, this, new BCLocalVariable[] { new BCLocalVariable(0) }, null);
				if (bcAttribute instanceof SecondConstantPool) {
//					System.out.println("Second constant pool detected.");
					constantPool.add(cp,(SecondConstantPool) bcAttribute);
				} else if (bcAttribute instanceof ClassInvariant) {
					System.out.println("Class invariant detected.");
					classInvariant = (ClassInvariant) bcAttribute;
				} else if (bcAttribute instanceof HistoryConstraints) {
					System.out.println("history constraints detected.");
					historyConstraints = (HistoryConstraints) bcAttribute;
				}
			}
		}
	}

//	// sets the super class of this class
//	public BCClass getSuperClass(IJml2bConfiguration config) {
//		if (superClass != null) {
//			return superClass;
//		}
//		superClass = ((B2JPackage) config.getPackage())
//				.getClass(superClassName);
//		return superClass;
//	}
//
//	// sets the interfaces implemented by this class
//	private void setInterfaces(IJml2bConfiguration config) {
//		if (interfaceNames == null) {
//			return;
//		}
//		if (interfaces != null) {
//			return;
//		}
//		interfaces = new HashMap();
//		for (int i = 0; i < interfaceNames.length; i++) {
//			BCClass _interface = ((B2JPackage) config.getPackage())
//					.getClass(interfaceNames[i]);
//			interfaces.put(interfaceNames[i], _interface);
//		}
//	}

	/**
	 * @return an object that represents constant pool of the class
	 */
	public BCConstantPool getConstantPool() {
		return constantPool;
	}

//	/**
//	 * NB : if a method with this signature is not found then may be an
//	 * exception must be thrown
//	 * 
//	 * @param signature
//	 * @return
//	 * @throws ReadAttributeException
//	 * @throws IllegalLoopException
//	 */
//	public BCMethod lookupMethod(IJml2bConfiguration config, String signature)
//			throws ReadAttributeException, IllegalLoopException {
//		BCMethod m = null;
//		/*
//		 * Util.dump("search for method " + signature + " in class " + className );
//		 * Util.dumpMethods(this);
//		 */
//		m = (BCMethod) methods.get(signature);
//		if (m != null) {
//			m.initMethod();
//			return m;
//		}
//		BCClass superClass = getSuperClass(config);
//		m = superClass.lookupMethod(config, signature);
//		if (m != null) {
//			return m;
//		}
//		BCClass interfaze;
//		for (int i = 0; i < interfaceNames.length; i++) {
//			interfaze = ((B2JPackage) config.getPackage())
//					.getClass(interfaceNames[i]);
//			m = (BCMethod) interfaze.lookupMethod(config, signature);
//			if (m != null) {
//				return m;
//			}
//		}
//		m.initMethod();
//		return m;
//	}
//
//	/**
//	 * searches for a field with name
//	 * 
//	 * @param fName
//	 * @return
//	 * @throws ReadAttributeException
//	 * @throws IllegalLoopException
//	 */
//	public BCField lookupField(IJml2bConfiguration config, String fName)
//			throws ReadAttributeException, IllegalLoopException {
//		BCField f = null;
//		/*
//		 * Util.dump("search for method " + signature + " in class " + className );
//		 * Util.dumpMethods(this);
//		 */
//		if (fields != null) {
//			for (int i = 0; i < fields.length; i++) {
//				if (fields[i].getName().equals(fName)) {
//					return fields[i];
//				}
//			}
//		}
//		/*
//		 * Util.dump("search for method " + signature + " in superclass " +
//		 * superClassName );
//		 */BCClass superClass = getSuperClass(config);
//		f = superClass.lookupField(config, fName);
//		if (f != null) {
//			return f;
//		}
//		BCClass interfaze;
//		for (int i = 0; i < interfaceNames.length; i++) {
//			interfaze = ((B2JPackage) config.getPackage())
//					.getClass(interfaceNames[i]);
//			f = interfaze.lookupField(config, fName);
//			if (f != null) {
//				return f;
//			}
//		}
//		return f;
//	}

	/**
	 * initialises the methods that are declared in this class
	 * 
	 * @param methods
	 */
	private void initMethods(Method[] _methods, ConstantPoolGen cp)
			throws ReadAttributeException {
//		methods = new HashMap();
		metody = new Vector<BCMethod>();
		for (int i = 0; i < _methods.length; i++) {
			MethodGen mg = new MethodGen(_methods[i], className, cp);
			BCMethod bcm = new BCMethod(mg, this, cp);
//			String key = MethodSignature.getSignature(bcm.getName(), bcm
//					.getArgTypes(), bcm.getReturnType());
//			methods.put(key, bcm);
			metody.addElement(bcm);
		}
	}
	
	public BCMethod getMethod(int i) {
		return metody.elementAt(i);
	}

//	public String getName() {
//		return className;
//	}
//
//	public void wp(IJml2bConfiguration config) throws ReadAttributeException,
//			IllegalLoopException {
//		Iterator miter = methods.values().iterator();
//		setConfig(config);
//		while (miter.hasNext()) {
//			BCMethod m = (BCMethod) miter.next();
//			Logger.out.println("wp for Method " + m.getName());
//			m.initMethod();
//			m.wp(config);
//
//		}
//	}
//
//	public Collection getMethodKeys() {
//		return methods.keySet();
//	}
//
//	/**
//	 * @return Returns the methods.
//	 */
//	public Collection getMethods() {
//		return methods.values();
//	}
//
//	/**
//	 * @return Returns the classInvariant.
//	 */
//	public ClassInvariant getClassInvariant() {
//		if (classInvariant == null) {
//			return null;
//		}
//		return classInvariant;
//	}
//
//	/*	*//**
//			 * @return Returns the classInvariant.
//			 */
//	/*
//	 * public Formula getClassInvariantAfterConstructor() { if (classInvariant ==
//	 * null) { return Predicate0Ar.TRUE; } return
//	 * classInvariant.getClassInvariantAfterInit(); }
//	 */
//
//	/**
//	 * @return Returns the historyConstraints.
//	 */
//	public Formula getHistoryConstraints() {
//		if (historyConstraints == null) {
//			return Predicate0Ar.TRUE;
//		}
//		return historyConstraints.getPredicate();
//	}
//
//	/**
//	 * @return Returns the fields.
//	 */
//	public BCField[] getFields() {
//		return fields;
//	}
//
//	public String toString() {
//		return getName();
//	}
//
//	/**
//	 * @param pt
//	 */
//	public void saveCode(PrintStream pt) {
//		// TODO Auto-generated method stub
//
//	}
//
//	public String getBName() {
//		return className;
//	}
//
//	public String getPackageName() {
//		return packageName;
//	}
}
