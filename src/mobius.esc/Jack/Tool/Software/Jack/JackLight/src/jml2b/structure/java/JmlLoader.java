//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JmlLoader.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.java;

import java.io.File;
import java.util.Stack;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.util.JmlFileEntry;
import jml2b.util.JmlPathEntry;
import jml2b.util.Profiler;

/** 
 * class used to load classes.
 * 
 * @author A. Requet
 */
public class JmlLoader extends Profiler {
	/** 
	 * Number of times a file is searched and not found. 
	 */
	public static int fileSearchMisses;

	/** 
	 * Extensions searched when loading a file. They are given by higher
	 * priority (For example, if a directory contains <code>C.java</code> and 
	 * <code>C.jml</code>, <code>C.jml</code> will be chosen first)
	 * <p>
	 * the following suffixes are not searched, since they are passive 
	 * suffixes:
	 * <ul>
	 *	<li><code>.spec-refined</code>,
	 *  <li><code>.jml-refined</code>,
	 *  <li><code>.java-refined</code>
	 * </ul>
	 */
	private static String[] jmlExtensions =
		{
			".spec",
			".jml",
			".refines-jml",
			".refines-spec",
			".refines-java",
			".java",
			".class"};

	/*@
	  @ invariant jmlPath != null;
	  @ invariant unlinkedFiles != null;
	  @ invariant defaultClasses != null;
	  @*/

	/** 
	 * Returns the class name from package <code>p</code>. 
	 * Loads the class if it is necessary. 
	 * The class is loaded as an "external" class.
	 * Returns <code>null</code> if the class could not be found.
	 * throws a <code>ClassLoadException</code> if a candidate file was found, 
	 * but could not be parsed.
	 */
	/*@
	  @ requires p != null;
	  @*/
	public static AClass loadClass(IJml2bConfiguration config,
									Package p,
									String name)
							throws Jml2bException {
		// get path corresponding to the package
		JmlFileEntry f = searchCandidateFile(config, p, name);
		
		if (f == null) {
			// no candidate file found.
			return null;
		}

		f.loadClass(config, config.getDefaultExternalFile());
		
		// return the class by looking for it in the package.
		AClass result = p.getClass(name);

		return result;
	}

//	/** 
//	 * Loads the class name using imports as the list of packages
//	 * where the class could be defined.
//	 * return <code>null</code> if the class could not be found.
//	 * <p>
//	 * throws <code>ClassLoadException</code> if a candidate file could be found, but
//	 * could not be loaded.
//	 */
//	/*@
//	  @ requires imports != null;
//	  @*/
//	public static Class loadClass(
//		IJml2bConfiguration config,
//		Enumeration imports,
//		String name)
//		throws Jml2bException {
//		Class loaded_class = null;
//
//		// look in each imported package
//		/*@
//		  @ loop_invariant true;
//		  @ loop_exsures (RuntimeException) false;
//		  @*/
//		while (imports.hasMoreElements()) {
//			Package tmp_pkg = (Package) imports.nextElement();
//
//			loaded_class = loadClass(config, tmp_pkg, name);
//
//			if (loaded_class != null) {
//				return loaded_class;
//			}
//		}
//		// try to load from java.lang as last resort since it is
//		// imported by default
//		return loadClass(config, Package.getJavaLang(), name);
//	}

	/** 
	 * Search a candidate file for the class name located in the package
	 * relative path <code>pkg_path</code>.
	 */
	/*@
	  @ requires p != null;
	  @*/
	public static JmlFileEntry searchCandidateFile(
		IJml2bConfiguration config,
		Package p,
		String name) {
		String pkg_path = p.getDirectory(config);
		JmlPathEntry[] jmlPath = config.getJmlPath();
		// look for a candidate file in each of the directory listed in 
		// jmlPath
		/*@
		  @ loop_invariant 0 <= i && i < jmlPath.length;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < jmlPath.length; ++i) {
//			String path = jmlPath[i] + pkg_path;

			// search for a file with the provided extensions
			for (int j = 0; j < jmlExtensions.length; ++j) {
				String file_name = name + jmlExtensions[j];
				File f = new File(pkg_path, file_name);
				
				JmlFileEntry is = jmlPath[i].checkFile(f);
				
				if (is != null) {
//					Logger.get().println("We have a winner! " + f);
					return is;
				}
				// increase the number of search that did not find the file
				++fileSearchMisses;
			}
		}
		return null;
	}

	/** 
	 * Checks that the given directory exists within the search path.
	 * It is used to check that added packages exists.
	 */
	public static boolean checkDirectory(
		IJml2bConfiguration config,
		String dir_name) {
		JmlPathEntry[] jmlPath = config.getJmlPath();
		/*@
		  @ loop_invariant 0 <= i && i < jmlPath.length;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < jmlPath.length; ++i) {
			if (jmlPath[i].checkDirectory(dir_name))
				return true;
		}
		return false;
	}

	/**
	 * Links statements for all the remaining files. Note that linking 
	 * statements for a file can trigger the loading of new files that will be 
	 * added to the stack of unlinked files.
	 */
	public static void linkStatements(IJml2bConfiguration config)
		throws Jml2bException {
		/*@
		  @ loop_invariant true;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		int errors = 0;
		while (!unlinkedFiles.empty()) {
			JmlFile file_to_link = (JmlFile) unlinkedFiles.pop();
			errors += file_to_link.linkStatements(config);
			if (errors == 0)
				file_to_link.typeCheck(config);
		}
	}

	/** 
	 * Load the given class, creating the package as needed.
	 * fqn has to be a fully qualified name.
	 * 
	 * @param config the configuration that should be used for loading 
	 *     new classes.
	 * @param fqn the fully qualified name of the class.
	 */
	/*@
	  @ requires fqn != null;
	  @*/
	public static AClass loadClass(IJml2bConfiguration config, String fqn)
		throws Jml2bException {
		// add packages if needed
		Package current = ((JavaLoader) config.getPackage()).getRoot();
		int last_index;
		int current_index = -1;
		String class_name;

		/*@
		  @ loop_modifies current;
		  @ loop_invariant current != null;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		do {
			last_index = current_index + 1;
			current_index = fqn.indexOf('.', last_index);

			if (current_index != -1) {
				// package => get the package, or create it if it does not
				// exists yet.
				String pkg_name = fqn.substring(last_index, current_index);
				//		Logger.get().println("Package : " + pkg_name);
				Package new_current = current.getPackage(pkg_name);

				if (new_current == null) {
					// package needs to be created
					new_current = new Package(pkg_name);
					current.addPackage((JavaLoader) config.getPackage(), new_current);
				}
				current = new_current;
			}
		} while (current_index != -1);

		// get the name of the class from the last index
		class_name = fqn.substring(last_index);
		//	Logger.get().println("Class : " + class_name);

		// at this point, the packages have been added. Load the class.
		return current.getAndLoadClass(config, class_name);
	}

	/** 
	 * Loads the default classes (ensures that they are loaded)
	 * 
	 * @param config the configuration that should be used for loading 
	 *    classes. 
	 */
	public static void loadDefaultClasses(IJml2bConfiguration config) {
		int count = defaultClasses.length;

		/*@
		  @ loop_invariant 0 <= i && i < defaultClasses.length;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < count; ++i) {
			try {
				loadClass(config, defaultClasses[i]);
			} catch (Jml2bException e) {
				throw new InternalError(
					"Cannot load class : "
						+ defaultClasses[i]
						+ "\n"
						+ e.getMessage());
			}
		}
	}

	/**
	 * Return true iff the given class exists in the given search path.
		 * The class is suposed to exist if a file with extension 
	 * <code>.java</code> or a jml recognised extension is found 
	 * in a subdirectory of the search path corresponding to the 
	 * package name of the class.
	 * 
	 * @param fqn the fully qualified name of the class
	 * @param search_path a list of path that should be searched for the 
	 * 		class.
	 * @return true iff the class can be found in the search path. 
	 */
	public static boolean classExists(String fqn, String[] path) {
		String class_name;
		String pkg_path;

		int class_index = fqn.lastIndexOf('.');
		if (class_index == -1) {
			class_name = fqn;
			pkg_path = "";
		} else {
			class_name = fqn.substring(class_index + 1);
			pkg_path = fqn.substring(0, class_index);
			pkg_path = pkg_path.replace('.', File.separatorChar);
		}

		/*@
		  @ loop_invariant 0 <= i && i < path.length;
		  @ loop_exsures (RuntimeException) false;
		  @*/
		for (int i = 0; i < path.length; ++i) {
			// for each path in the search path
			File current_path = new File(path[i], pkg_path);

			/*@
			  @ loop_invariant 0 <= j && j < jmlExtensions.length;
			  @ loop_exsures (RuntimeException) false;
			  @*/
			for (int j = 0; j < jmlExtensions.length; ++j) {
				File current =
					new File(current_path, class_name + jmlExtensions[j]);
				if (current.exists()) {
					return true;
				}
			}

		}

		return false;
	}

//	/**
//	 * Return true iff the given class exists in the given search path.
//	 * The class is suposed to exist if a file with extension 
//	 * <code>.java</code> or a jml recognised extension is found 
//	 * in a subdirectory of the search path corresponding to the 
//	 * package name of the class.
//	 * 
//	 * @param fqn the fully qualified name of the class
//	 * @param search_path a list of path that should be searched for the 
//	 * 		class.
//	 * @return true iff the class can be found in the search path. 
//	 */
//	/*@
//	  @ requires fqn != null;
//	  @*/
//	public static boolean classExists(String fqn, String search_path) {
//		String[] path = Util.tokenize(search_path, File.pathSeparator);
//		return classExists(fqn, path);
//	}

	/**
	 * Loads classes from the given serialized image.
	 * 
	 * @return false in case of error. true otherwise.
	 */
	public static boolean loadSerializedImage(IJml2bConfiguration config, String image_file) {
		return ((JavaLoader) config.getPackage()).initFromFile(image_file);
	}

	/**
	 * Remove any unlinked file from the unlinkedFiles stack.
	 */
	public static void clearAll() {
		unlinkedFiles.clear();
	}

	/**
	 *  files that don't have linked statements
	 */
	public static Stack unlinkedFiles = new Stack();

	public static final String[] defaultClasses =
		{
			"java.lang.Object",
			"java.lang.Cloneable",
			"java.lang.NullPointerException",
			"java.lang.ArithmeticException",
			"java.lang.ArrayIndexOutOfBoundsException",
			"java.lang.NegativeArraySizeException",
			"java.lang.ClassCastException",
			"java.lang.ArrayStoreException",
			"java.lang.RuntimeException",
			"java.io.Serializable",
			"java.io.ArrayStoreException" };

}
