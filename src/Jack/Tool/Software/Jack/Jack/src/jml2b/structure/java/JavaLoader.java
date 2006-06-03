package jml2b.structure.java;

import jack.util.Logger;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;

import jml2b.structure.IClass;
import jml2b.structure.IPackage;

public class JavaLoader implements IPackage {

	private /*@ spec_public */
	Package rootPackage = null;

	private /*@ spec_public */
	Package javaLang = null;

	/*@ private invariant (rootPackage != null) == (javaLang != null);
	  @*/

	public IClass getJavaLangString() {
			return getJavaLang().getClass("String");
	}

	// return the Package object corresponding to java.lang.
	public Package getJavaLang() {
		if (javaLang == null) {
			createDefaultPackages();
		}
		return javaLang;
	}

	// return the root package.
	public Package getRoot() {
		if (rootPackage == null) {
			createDefaultPackages();
		}
		return rootPackage;
	}

	// create the default packages. That is, the root package as well as
	// the java.lang package. (it also creates the java package)
	/*@ 
	  @ ensures rootPackage != null && javaLang != null;
	  @*/
	private void createDefaultPackages() {
		// create root package, as well as the default java.lang package
		rootPackage = new Package(null);
		Package java = new Package("java");
		javaLang = new Package("lang");
		rootPackage.addPackage(this, java);
		java.addPackage(this, javaLang);
	}

	/*@ 
	  @ ensures \result == ((rootPackage != null) && (javaLang != null));
	  @*/
	public boolean restoreDefaultPackages(Package root) {
		Package java_lang = (Package) root.getPackage("java");
		if (java_lang == null) {
			return false;
		}
		java_lang = java_lang.getPackage("lang");
		if (java_lang == null) {
			return false;
		}

		// initialize default packages
		rootPackage = root;
		javaLang = java_lang;

		return true;
	}

	/** 
	 * Inits the root package (java.lang, etc...) from the given serialized
	 * file.
	 * return true on success, false otherwise.
	 */
	public boolean initFromFile(String file_name) {
		Package root = null;

		try {
			FileInputStream is = new FileInputStream(file_name);
			ObjectInputStream os = new ObjectInputStream(is);
			root = (Package) os.readObject();
		} catch (IOException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return false;
		} catch (ClassCastException e) {
			// error when casting to package
			Logger.err.println("Exception catched : " + e.toString());
			return false;
		} catch (ClassNotFoundException e) {
			Logger.err.println("Exception catched : " + e.toString());
			return false;
		}

		if (root == null) {
			return false;
		}

		return restoreDefaultPackages(root);
	}


}
