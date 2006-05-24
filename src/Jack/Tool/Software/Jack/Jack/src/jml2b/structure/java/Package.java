//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Package.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.structure.java;

import java.io.File;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;

/** 
 * class representing packages.
 * It is the class from where all the known information is accessible.
 * @author A. Requet
 */
public class Package extends NamedNode implements Serializable {
	/**
	 * If this value is true, then each package will maintain a list of classes
	 * that are known not to belong to the package.
	 */
	protected static final boolean storeMisses = true;

	/**
	 * Set of classes that do not belongs to the package.
	 * this sets contains Strings corresponding to the name of the classes.
	 */
	protected Set classMisses;

	/** 
	 * Short name of the package.
	 */
	public String name;
	
	private String fullyQualifiedName;

	/** 
	 * The parent package. 
	 */
	public Package parent;

	/**
	 * Vector storing the classes defined in the package.
	 */
	private Vector classes;
	/** 
	 * Subpackages contained within this package. 
	 */
	Vector subPackages;

	/** 
	 * <code>true</code> if the package fields from this package 
	 * should be kept when loading classes.
	 */
	boolean keepPackage;

	/**
	 * Creates a new empty package.
	 */
	private Package() {
		super(new ParsedItem());
		classes = new Vector();
		subPackages = new Vector();
		keepPackage = false;
		if (storeMisses) {
			classMisses = new HashSet();
		}
	}

	public Package(String name) {
		super(new ParsedItem());
		classes = new Vector();
		subPackages = new Vector();
		this.name = name;
		keepPackage = false;
		if (storeMisses) {
			classMisses = new HashSet();
		}
	}

	public Enumeration getSubPackages() {
		return subPackages.elements();
	}

	public Enumeration getClasses() {
		return classes.elements();
	}

	public String getName() {
		return name;
	}

	public Package getParent() {
		return parent;
	}

	public boolean keepPackageVisible() {
		return keepPackage;
	}

	public void setKeepPackage(boolean val) {
		keepPackage = val;
	}

	/** 
	 * Return the number of classes in this package. If include_subpackage is
	 * true, count the number of classes in the subpackages.
	 */
	public int getClassCount(boolean include_subpackages) {
		int count = classes.size();
		if (include_subpackages) {
			Enumeration e = subPackages.elements();
			while (e.hasMoreElements()) {
				Package p = (Package) e.nextElement();
				count += p.getClassCount(true);
			}
		}
		return count;
	}

	public void addPackage(JavaLoader jl, Package p) {
		// update the parent package
		p.parent = this;
		p.setFullyQualifiedName(jl); 
		// add the package
		subPackages.add(p);

		//		Debug.println(Debug.PACKAGES, 
		//				      "Added package " + p.getName() + " to package " +
		//				      getName());
	}

	public void addClass(AClass c) {
		classes.add(c);
		//		Debug.println(Debug.PACKAGES,
		//			      "Added class " + c.getName() + 
		//		    	  " to package " + getName());
	}

	/** 
	 * Search for the given package inside this package.  Note that
	 * name has to be the short name of the package (i.e. not the fully
	 * qualified name) 
	 * @return the package with the given name, null if it is not found. 
	 */
	public Package getPackage(String name) {
		Enumeration e = subPackages.elements();
		Package pkg;
		while (e.hasMoreElements()) {
			pkg = (Package) e.nextElement();
			if (name.equals(pkg.getName())) {
				return pkg;
			}
		}
		return null;
	}

	/** 
	 * Return true if the package with the given name exists. 
	 */
	boolean packageExists(String name) {
		return getPackage(name) != null;
	}

	/** 
	 * Search for the given class inside this package. Note that name
	 * has to be the short name of the class (i.e. not the fully
	 * qualified name).
	 *
	 * @return the class with the given name, null if it is not found. 
	 */
	public AClass getClass(String name) {
		Enumeration e = classes.elements();
		AClass cl;
		while (e.hasMoreElements()) {
			cl = (AClass) e.nextElement();
			if (name.equals(cl.getName())) {
				return cl;
			}
		}
		return null;
	}

	/** 
	 * Check that the package name exists and create the subpackage if it
	 * does.
	 */
	public Package createAndCheckSubPackage(
		IJml2bConfiguration config,
		String name) {
		Package result = getPackage(name);
		if (result != null) {
			return result;
		}

		// the package does not exists yet. Verify that there exists a
		// corresponding directory in the file system.
		String directory = getDirectory(config) + File.separator + name;
		if (JmlLoader.checkDirectory(config, directory)) {
			result = new Package(name);
			addPackage((JavaLoader) config.getPackage(), result);

			return result;
		}
		return null;
	}

	public Package getAndLoadPackage(JavaLoader jl, String name) {
		return createSubPackage(jl, name);
	}

	/** 
	 * Return a reference to the class name. This method will try to load
	 * the class if name cannot be found.
	 * return null If the class cannot be found neither in the loaded classes nor on
	 * the disk.
	 * Throws ClassLoadError if a candidate class was found on the disk,
	 * but could not be loaded
	 */
	public AClass getAndLoadClass(IJml2bConfiguration config, String name)
		throws Jml2bException {
		AClass result;
		
		result = getClass(name);
		if (result != null) {
			return result;
		}
		// check that the class is not in the list of classes already tried
		if (storeMisses && classMisses.contains(name)) {
			// don't try again to load this class
			return null;
		}
		result = JmlLoader.loadClass(config, this, name);
		if (storeMisses && result == null) {
			// if the class could not be loaded, add it to the list of classes
			// that are not in the package
			classMisses.add(name);
		}
		return result;
	}

	/**
	 * Returns the fully qualified name of this package.
	 */
	public void setFullyQualifiedName(JavaLoader jl) {
		if (this == jl.getRoot())
			fullyQualifiedName =  null;
		else {
			String parent_path = parent.getFullyQualifiedName();
			
			if (parent_path != null) {
				fullyQualifiedName =  parent_path + "." + getName();
			}
			else
				fullyQualifiedName = getName();
		}
	}

	public String getFullyQualifiedName() {
		return fullyQualifiedName;
	}

		/** 
	 * return the directory corresponding to this package. 
	 * return null if the package is the root package
	 */
	public String getDirectory(IJml2bConfiguration config) {
		if (this == ((JavaLoader) config.getPackage()).getRoot()) {
			return ""; //File.separator;
		} else if (parent == ((JavaLoader) config.getPackage()).getRoot())
			return getName();
		else
			return parent.getDirectory(config) + File.separator + getName();
	}

	public Package createSubPackage(JavaLoader jl, String name) {
		Package p = getPackage(name);
		if (p != null) {
			return p;
		}
		p = new Package(name);
		addPackage(jl, p);
		return p;
	}


//	/** 
//	 * Unload all the loaded packages.
//	 */
//	/*@ 
//	  @ ensures rootPackage == null && javaLang == null;
//	  @*/
//	public void clearAll() {
//		javaLang = null;
//		rootPackage = null;
//		Type.clearAll();
//		Class.clearAll();
//		JmlLoader.clearAll();
//	}

//	public static Package initPackage() {
//		Package res = new Package();
//		res.javaLang = null;
//		res.rootPackage = null;
////		Type.clearAll();
////		Class.clearAll();
//		JmlLoader.clearAll();
//		return res;
//	}
	
	public AClass searchClass(String s) {
		if (s.indexOf('/') != -1) {
			return getPackage(s.substring(0, s.indexOf('/'))).searchClass(
				s.substring(s.indexOf('/') + 1));
		} else
			return getClass(s);
	}

	static final long serialVersionUID = -4244945142001918487L;

}
