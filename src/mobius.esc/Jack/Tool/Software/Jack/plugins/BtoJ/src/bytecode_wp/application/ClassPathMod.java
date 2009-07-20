/*
 * Created on Mar 25, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package bytecode_wp.application;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.net.URLClassLoader;

/**
 * @author jcharles
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class ClassPathMod extends URLClassLoader{
	 
	/**
	 * @param urls
	 * @param parent
	 */
	public ClassPathMod(ClassLoader parent) {
		super(new URL[0], parent);
		// TODO Auto-generated constructor stub
	}
	 
	public void addFile(String s) throws IOException {
		File f = new File(s);
		addFile(f);
	}//end method
	 
	public void addFile(File f) throws IOException {
		addURL(f.toURL());
	}//end method
	 
	
	
	 
	 
	}//end class

