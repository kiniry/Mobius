/*
 * Created on Feb 9, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.util;

import java.io.File;
import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ClassLoadException;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.bytecode.ClassFile;

import org.apache.bcel.classfile.ClassParser;

/**
 * 
 * @author L. Burdy
 */
public class JmlClassEntryFile extends JmlFileEntry {

	String jarFile;
	String className;
	/**
	 * @param jarFile
	 * @param path
	 */
	public JmlClassEntryFile(String jarFile, String path) {
		this.jarFile = jarFile;
		className = path;
	}

	public File getFile() {
		return new File(jarFile);
	}

	public String getName() {
		return jarFile + "_" + className;
	}

	public String getAbsolutePath() {
		return jarFile + "_" + className;
	}

	public void loadClass(IJml2bConfiguration config, boolean defaultExternalFile) throws ClassLoadException,
			Jml2bException {
		ClassFile jml  = null;
		// load the jml file as an external file
		try {
		jml = loadFile();
		}
		catch (IOException ioe)
		{
			throw new ClassLoadException("Error reading file: " + getName() + "(" + ioe.getMessage() + ")");
		}

		// parse and link the loaded file
//		try {
			jml.parse(config);
//		} catch (InternalError ie) {
//			ErrorHandler.error(jml, -1, -1, ie.toString());
//		}
		jml.link(config);

	}

	/**
	 * @return
	 */
	private ClassFile loadFile() throws IOException {
		ClassParser cp = new ClassParser(jarFile, className);
		return new ClassFile(cp.parse());
	}


}