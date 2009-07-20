/*
 * Created on Apr 26, 2004
 *
 * the class represents a whole java application
 */
package bytecode_wp.application;
import jack.util.Logger;

import java.util.Hashtable;

import jml2b.structure.IClass;
import jml2b.structure.IPackage;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassLoaderRepository;

import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.BCClass;

/**
 * @author mpavlova
 *
 * this class models a class loader for the classes that are verified
 */
public class JavaClassLoader implements IPackage {

	// contains all the classes that are loaded already
	// a class is loaded only once
	Hashtable classes;
	ClassLoader loader;
	ClassLoaderRepository repos;
	
//	public static final JavaApplication Application = new JavaApplication(ClassLoader.getSystemClassLoader());
	
	public JavaClassLoader(ClassLoader cl) {
		loader = cl;
		repos = new ClassLoaderRepository(cl);
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
			Logger.err.print(exc.getMessage());
		}
		return _class;
	}

	private BCClass addClass(String _name) throws ReadAttributeException {
		if (classes == null) {
			classes = new Hashtable();
		}
		JavaClass clazz = null;
		try {
			clazz = repos.loadClass(_name);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		//TODO commented temporarily 
		//clazz = repos.findClass(_name);
		BCClass bcClass = new BCClass(clazz);
		classes.put(_name, bcClass);
		return bcClass;
	}

	/**
	 * @return Returns the classes.
	 */
	public Hashtable getClasses() {
		return classes;
	}

	public IClass getJavaLangString() {
		return (BCClass)classes.get("java.lang.String");
	}


}
