///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ImageGenerator.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jack.plugin;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.lang.reflect.InvocationTargetException;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlLoader;
import jml2b.structure.java.Package;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.operation.IRunnableWithProgress;

/**
 * Class allowing to generate a Serialized image of the default classes.
 * 
 * @author A. Requet
 */
public class ImageGenerator
	extends RunnableWithError
	implements IRunnableWithProgress {
		
	/** 
	 * Vector storing Strings corresponding to the fully qualified 
	 * name of classes that should be added to the image.
	 */
	Vector additionalClasses;

	/** 
	 * The file where the image should be written.
	 */
	private File outputFile;

	/**
	 * The project for which the image is generated. It is used to access the
	 * project dependant settings such as JML path or output subdirectory.
	 */
//	private IProject project;

	private IJml2bConfiguration configuration;

	ImageGenerator(IJavaProject project, File output_file) {
		additionalClasses = new Vector();
		outputFile = output_file;
//		this.project = project;
		configuration = new JackJml2bConfiguration(project,  new JavaLoader());
	}

	void setOutputFile(File output_file) {
		outputFile = output_file;
	}

	public void setClasses(String[] classes) {
		additionalClasses.ensureCapacity(classes.length);
		for (int i = 0; i < classes.length; ++i) {
			additionalClasses.add(classes[i]);
		}
	}

	void writeOutput() {
		// get the ouput file
		ObjectOutputStream ostream = null;
		try {
			FileOutputStream stream = new FileOutputStream(outputFile);
			ostream = new ObjectOutputStream(stream);

			ostream.writeObject(((JavaLoader) configuration.getPackage()).getRoot());
			ostream.close();
		} catch (IOException e) {
			setError("IOException catched: " + e.toString());
			if (ostream != null) {
				try {
					ostream.close();
				} catch (IOException e2) {
					setError(
						"IOException catched: "
							+ e.toString()
							+ "\nAdditional exception catched when trying to close file : "
							+ e2.toString());
				}
			}
		}
	}

	/** 
	 * Adds the given class to the list of additional classes that
	 * should be included in the image.
	 * 
	 * @param added_class the fully qualified name of the class.
	 */
	void addClass(String added_class) {
		additionalClasses.add(added_class);
	}

	/**
	 * Load the given class.
	 * 
	 * @param fqn the fully qualified name of the class.
	 * @return true if load success, false otherwise.
	 */
	private boolean loadClass(String fqn) {
		// add packages if needed
		Package current = ((JavaLoader) configuration.getPackage()).getRoot();
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
					current.addPackage((JavaLoader) configuration.getPackage(), new_current);
				}
				current = new_current;
			}
		} while (current_index != -1);

		// get the name of the class from the last index
		class_name = fqn.substring(last_index);
		//	Logger.get().println("Class : " + class_name);

		// at this point, the packages have been added. Load the class.
		try {
			if (current.getAndLoadClass(configuration, class_name) == null) {
				return false;
			}
		} catch (Jml2bException e) {
			return false;
		}

		return true;
	}

	/**
	 * Load the default classes. That is, <code>Object</code> and its related 
	 * classes as well as the standard exception types.
	 */
	boolean loadDefaultClasses() {
		try {
			JmlLoader.loadDefaultClasses(configuration);
		} catch (jml2b.exceptions.InternalError e) {
			setError(
				"Could not load default classes\n"
					+ "check that your JML search path is correct\n"
					+ "Exception catched : "
					+ e.toString());
			return false;
		}
		return true;
	}

	/**
	 * @see org.eclipse.jface.operation.IRunnableWithProgress#run(IProgressMonitor)
	 */
	//@ requires outputFile != null;
	public void run(IProgressMonitor monitor)
		throws InvocationTargetException, InterruptedException {
		monitor.beginTask("Generating image", IProgressMonitor.UNKNOWN);
		monitor.subTask("Loading default classes");

		// clears all the  loaded classes		
		//Package p = Package.initPackage();//.clearAll();

		if (!loadDefaultClasses()) {
			monitor.done();
//			Package.clearAll();
			return;
		}

		if (monitor.isCanceled()) {
//			Package.clearAll();
			return;
		}

		monitor.subTask("Linking remaining statements");
		try {
			JmlLoader.linkStatements(configuration);
		} catch (Jml2bException e) {
			setError("Error linking statements");
//			Package.clearAll();
			return;
		}

		if (monitor.isCanceled()) {
//			Package.clearAll();
			return;
		}

		// load the additional classes
		Enumeration e = additionalClasses.elements();
		while (e.hasMoreElements()) {
			String class_name = (String) e.nextElement();
			monitor.subTask("Loading additional classes : " + class_name);
			if (!loadClass(class_name)) {
				setError("Error loading: " + class_name);
//				Package.clearAll();
				return;
			}
			if (monitor.isCanceled()) {
//				Package.clearAll();
				return;
			}
		}

		monitor.subTask("Linking remaining statements");
		try {
			JmlLoader.linkStatements(configuration);
		} catch (Jml2bException ex) {
			setError("Error linking statements" + ex.toString());
//			Package.clearAll();
			return;
		}

		if (monitor.isCanceled()) {
//			Package.clearAll();
			return;
		}

		monitor.subTask("Saving image");

		writeOutput();
//		Package.clearAll();

		monitor.done();
	}
}