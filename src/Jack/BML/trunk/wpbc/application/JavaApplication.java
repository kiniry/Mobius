/*
 * Created on Apr 26, 2004
 *
 * the class represents a whole java application
 */
package application;

import java.util.HashMap;

import org.apache.bcel.Repository;
import org.apache.bcel.classfile.JavaClass;

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
	private static HashMap classes;
	
	public static BCClass getClass(String _name ) {
		BCClass _class = null;
		if (classes == null) {
			_class = addClass(_name);
			return _class;
		}
		if ( classes.get(_name) != null)  {
			return (BCClass)classes.get(_name);
		}	
		_class = addClass(_name);
		return _class;
	}
	
	private static BCClass addClass(String _name)  {
		if (classes == null) {
			classes = new HashMap();
		}
		JavaClass clazz = Repository.lookupClass(_name);
		BCClass bcClass = new BCClass(clazz);
		classes.put(_name, bcClass);
		return bcClass;
	}

}
