/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;


import java.util.HashMap;
import java.util.Iterator;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;

import utils.Util;

import application.JavaApplication;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCClass {
	private HashMap methods;
	private HashMap fields;
	
	private String className;
	
	private String[] interfaceNames;
	private String superClassName;
	
	private BCConstantPool constantPool;
	private BCConstantPool secondConstantPool;;
	
	
	private BCClass superClass;
	
	private HashMap interfaces;
	
	
	public BCClass( JavaClass _clazz)  {
		className = _clazz.getClassName();
		ConstantPoolGen cpg = new ConstantPoolGen(_clazz.getConstantPool());
		constantPool = new BCConstantPool(cpg);
		Method[] methods = _clazz.getMethods();
		initMethods(methods, cpg);
	}
	
	
	//sets the super class of this class
	private void setSuperClass(  JavaClass _clazz ) {
	
	}
	
	//sets the interfaces implemented by this class
	private void setInterfaces(  JavaClass _clazz ) {
	
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
	 */
	public BCMethod lookupMethod( String signature ) {
		
		BCMethod m = null;
		m = getMethod(signature);
		if ( m != null) {
			return m;
		}
		
		m = superClass.lookupMethod(signature);
		if ( m != null) {
			return m;
		}
		return m;
	}

	/**
	 * @return
	 */
	public BCMethod getMethod(String signature) {
		BCMethod _m = (BCMethod) methods.get(signature);
		if (_m != null) {
			return _m;
		}
		BCClass superClass = JavaApplication.getClass(superClassName);
		_m = (BCMethod)superClass.getMethod(signature);
		if (_m != null) {
			return _m;
		}
		BCClass interfaze;
		for (int i = 0; i < interfaceNames.length; i++) {
			interfaze =  JavaApplication.getClass(interfaceNames[i]);
			_m = (BCMethod)interfaze.getMethod(signature);
			if (_m != null) {
				return _m;
			}
		}
		//should ion fact throw exception if there is no such a method
		return null;
	}


	/**
	 * @param methods
	 */
	private void initMethods(Method[] _methods, ConstantPoolGen cp)  {
		methods = new HashMap();
	//	for (int i = 0; i < _methods.length; i++)  {
			MethodGen mg = new MethodGen(_methods[2], className, cp);
			Util.dump("methodName ---   "  + mg.getName() + "   ---");
			BCMethod bcm = new BCMethod( mg, cp, constantPool) ;
			bcm.initTrace();
			methods.put(mg.getSignature(), bcm);
		//}
	}
	
	/**
	 * @param methods
	 */
	private void initFields(Field[] _fields, ConstantPoolGen cp)  {
		fields = new HashMap();
		for (int i = 0; i < _fields.length; i++)  {
					
		//
		}
	}
	
	
	
	public void  wp() {
		Iterator  miter = methods.values().iterator() ;
		while ( miter.hasNext()) {
			BCMethod m = (BCMethod)miter.next(); 
			m.wp();
		}
	}
 
}
