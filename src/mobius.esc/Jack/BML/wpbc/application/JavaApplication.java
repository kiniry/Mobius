/*
 * Created on Apr 26, 2004
 *
 * the class represents a whole java application
 */
package application;

import java.util.Enumeration;

import java.util.Hashtable;

import org.apache.bcel.Repository;
import org.apache.bcel.classfile.JavaClass;

import utils.Util;

import bc.io.ReadAttributeException;
import bcclass.BCClass;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class JavaApplication {

	// contains all the classes that are loaded already
	// a class is loaded only once
	Hashtable classes;

	public static final JavaApplication Application = new JavaApplication();

	private JavaApplication() {
	}

	public BCClass getClass(String _name)  {
		BCClass _class = null;
		try {
			if (classes == null) {
				_class = addClass(_name);
				return _class;
			}
			_class= (BCClass)classes.get(_name); 
			if (_class != null) {
				return _class;
			}
			_class = addClass(_name);
		} catch (ReadAttributeException exc) {
			System.err.print(exc.getMessage());
		}
		return _class;
	}

	private BCClass addClass(String _name) throws ReadAttributeException {
		if (classes == null) {
			classes = new Hashtable();
		}
		Enumeration enum = classes.keys();
		while (enum.hasMoreElements()) {
			String n = (String) enum.nextElement();
			
		}
		
		JavaClass clazz = Repository.lookupClass(_name);
		/*Util.dump("ADD CLASS WITH NAME " + "----" + _name + "----");*/
		BCClass bcClass = new BCClass(clazz);
		classes.put(_name, bcClass);
		return bcClass;
	}

	/**
	 * @return Returns the classes.
	 */
	public Enumeration getClasses() {
		return classes.elements();
	}
}
