///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: Serializer.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b;

import jack.util.Logger;

import java.io.File;
import java.io.FileOutputStream;
import java.io.ObjectOutputStream;

import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.JmlLoader;
import jml2b.structure.java.Package;
import jml2b.util.Profiler;
import jml2b.util.Util;

/**
 *  Simple application loading the java.lang classes and serializing them
 *  using the Java serialisation mechanism. 
 * @author A. Requet
 */
public class Serializer extends Profiler {
	static String usage[] =
		{
			"Usage: java jml2b/Serializer <classes> output_file",
			"    dump a serialized image of the packages and classes referenced",
			"    by the given classes to output_file.",
			"    classes is a list of fully-qualified names of classes or interfaces.",
			"    If classes is not set, the classes referenced by java.lang.Object",
			"    are used",
			"",
			"    examples:",
			"    Serializer image.img",
			"      dump the classes referenced by java.lang.Object to image.img",
			"",
			"    Serializer java.util.Vector java.util.Enumeration image.img",
			"      dump the classes referenced by java.lang.Object, java.util.Vector",
			"      and java.util.Enumeration to image.img" };

	public static void displayUsage() {
		for (int i = 0; i < usage.length; ++i) {
			Logger.get().println(usage[i]);
		}
	}

	public static void loadClass(IJml2bConfiguration config, String fqn)
		throws Jml2bException {
		// add packages if needed
		Package current = ((JavaLoader) config.getPackage()).getRoot();
		int last_index;
		int current_index = -1;
		String class_name;

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
		if (current.getAndLoadClass(config, class_name) == null) {
			throw new Jml2bException("Cannot load class: " + fqn);
		}
	}

	public static void main(String argv[]) {
		String[] jmlPath = null;

		if (argv.length < 1) {
			displayUsage();
			System.exit(0);
		}

		long start_time = 0;
		long linking_time = 0;
		long end_time = 0;

		int extra_classes_count = argv.length - 1;

		// set jml search path
		String jml_path_list = System.getProperty("jml2b.jmlpath");
		if (jml_path_list != null) {
			jmlPath = Util.tokenize(jml_path_list, File.pathSeparator);
		}

		Jml2bConfig config = new Jml2bConfig(jmlPath);
		File output_file = new File(argv[extra_classes_count]);

		try {
			Logger.get().println("Loading default classes");
			// get the Object type. This forces the loading, parsing
			// and linking of the Object class, as well as all the
			// classes it references
			start_time = System.currentTimeMillis();
			JmlLoader.loadDefaultClasses(config);

			linking_time = System.currentTimeMillis();

			// finalize the loading of the objects.
			Logger.get().println("Linking remaining statements");
			JmlLoader.linkStatements(config);

			end_time = System.currentTimeMillis();
		} catch (Jml2bException e) {
			Logger.err.println("Catched exception:");
			Logger.err.println(e.toString());
			System.exit(1);
		}

		// load the extra classes specified on the command line.
		for (int i = 0; i < extra_classes_count; ++i) {
			try {
				loadClass(config, argv[i]);
			} catch (Jml2bException e) {
				Logger.err.println("Exception catched : " + e.toString());
			}
		}

		try {
			// link the remaining statements.
			JmlLoader.linkStatements(config);

			// print informations.
			Logger.get().println("Loading time : " + (linking_time - start_time));
			Logger.get().println(
				"JML Parser time : " + JmlFile.getJmlParserTime());
			Logger.get().println(
				"Statement Linking time : " + (end_time - linking_time));
			Logger.get().println("Total time : " + (end_time - start_time));

			FileOutputStream stream = new FileOutputStream(output_file);
			ObjectOutputStream ostream = new ObjectOutputStream(stream);

			ostream.writeObject(((JavaLoader) config.getPackage()).getRoot());
			ostream.close();
		} catch (Exception e) {
			// catch Jml2bExceptions as well as IOExceptions.
			Logger.err.println("Exception catched");
			Logger.err.println("    " + e.toString());
		}
	}
}