/*
 * Created on Jun 8, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package bytecode_to_JPO;

import jack.util.Logger;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.structure.IClass;
import jml2b.structure.IPackage;
import bytecode_wp.application.JavaClassLoader;
import bytecode_wp.bcclass.BCClass;

public class B2JPackage implements IPackage {

	JavaClassLoader loader;
	
	Vector loadedClasses;
	
	public B2JPackage(JavaClassLoader loader) {
		this.loader = loader;
		loadedClasses = new Vector();
	}

	public IClass getJavaLangString() {
		return loader.getJavaLangString();
	}

	public BCClass getClass(String _name)  {
		return loader.getClass( _name);
	}
	
	public Hashtable getClasses() {
		return loader.getClasses();
	}

	public B2JClass search(String name) {
		Enumeration e = loadedClasses.elements();
		while (e.hasMoreElements()) {
			B2JClass c = (B2JClass) e.nextElement();
			if (c.getBName().equals("c_" + name.replace('.', '_')))
				return c;
		}
		return null;
	}
	
	public B2JClass addB2JClass(IJml2bConfiguration config, BCClass clazz, boolean b) {
		B2JClass c = search(clazz.getName());
		if (c == null) {
			c = new B2JClass(config, clazz);
			
			loadedClasses.add(c);
			c.init(clazz, true);
		}
		return c;
	}
	
	
	public B2JClass addB2JClass(IJml2bConfiguration config, String name, boolean b) {
		B2JClass c;
		if ((c = search(name)) == null) {
			BCClass clazz = loader.getClass( name);
			c = new B2JClass(config, clazz, b);
			loadedClasses.add(c);
		}
		return c;
	}
}
