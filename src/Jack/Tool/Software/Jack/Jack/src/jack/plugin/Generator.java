//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Generator.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jack.plugin;

import jack.plugin.compile.PoGeneratorErrorHandler;
import jack.util.Logger;

import java.io.File;
import java.util.Iterator;
import java.util.Vector;

import jml2b.exceptions.ClassLoadException;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.JmlLoader;
import jml2b.util.JmlEntryFile;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.operation.IRunnableWithProgress;

/**
 * This class loads and links a JML file.
 * 
 * @author A. Requet, L. Burdy
 **/
public abstract class Generator
	extends RunnableWithError
	implements IRunnableWithProgress {

	/**
	 * The key that is used for storing the eclipse resource corresponding to
	 * the jml file.
	 */
	public static final String ECLIPSE_RESOURCE_KEY =
		"jack.plugin.eclipseresource";

	/**
	 * The type of markers that are used by Jack.
	 */
	public static final String PROBLEM_MARKER_TYPE = "jack.plugin.jackproblem";

	/**
	 * The current error handler.
	 */
	private ErrorHandler handler;

	/**
	 * The project corresponding to the files that are processed.
	 */
	protected IProject project;

	/**
	 * The Java project corresponding to the file that are processed if they are 
	 * compilation units, null otherwise.
	 */
	protected IJavaProject javaProject;

	/**
	 * The current configuration
	 */
	protected JackJml2bConfiguration configuration;


	/**
	 * The set of processed ressources (IRessource).
	 */
	private Vector compilationUnits;

	/**
	 * The name of the current task to display in the monitor.
	 **/
	private String taskName;

	/** 
	 * Create a new Generator allowing to load and link given compilation units.
	 * @param compilation_units the compilations units that have to loaded and linked.
	 **/
	public Generator(Iterator compilation_units) {
		// copy the compilation units into the compilationUnits vector
		compilationUnits = new Vector();

		while (compilation_units.hasNext()) {
			Object o = compilation_units.next();
			if (o instanceof ICompilationUnit) {
				compilationUnits.add(((ICompilationUnit) o).getResource());
				javaProject = ((ICompilationUnit) o).getJavaProject();
				project = javaProject.getProject();
			} else if (o instanceof IResource) {
				compilationUnits.add(o);
				project = ((IResource) o).getProject();
			} else
				throw new InternalError("Unknow selectedItem " + o);
		}

		if (compilationUnits.size() == 0) {
			// should never happen
			return;
		}

		configuration = new JackJml2bConfiguration(javaProject, new JavaLoader());
	}

	public Generator(ICompilationUnit c, String task) {
		// copy the compilation units into the compilationUnits vector
		compilationUnits = new Vector();

		compilationUnits.add(c.getResource());
		javaProject = c.getJavaProject();
		project = javaProject.getProject();
		configuration = new JackJml2bConfiguration(javaProject, new JavaLoader());
		taskName = task;
	}

	/**
	 * Return the error handler that should be used by the parser and PO 
	 * generator.
	 */
	//@ requires project != null;
	private ErrorHandler getErrorHandler() {
		if (handler == null) {
			handler = new PoGeneratorErrorHandler(project);
		}
		return handler;
	}

	/** 
	 * Returns the name of the serialised image file. Returns <code>null</code> 
	 * if no serialized image is specified.
	 */
	//@ requires javaProject != null;
	protected String getSerializedImageFile() {
		IResource resource = project /*.getResource()*/;

		try {
			String value =
				resource.getPersistentProperty(
					JackPlugin.USE_SERIALIZED_IMAGE_PROPERTY);
			if (value == null || !value.equals("true")) {
				return null;
			}
		} catch (CoreException e) {
			Logger.err.println("CoreException catched: " + e.toString());
			return null;
		}

		// if we reach this point, we want to use a Serialized image.
		// get the file.
		IFolder folder = getAndCreateOutputDir();

		File f = folder.getLocation().toFile();
		File result = new File(f, JackPlugin.IMAGE_NAME);

		//return result.exists() ? result.toString() : null;

		// don't check if the file exists so that an error is popped if
		// the image is not generated.
		return result.toString();
	}

	/**
	 * Loads the default classes.
	 * 
	 * @return true in case of success, false otherwise.
	 */
	public boolean loadDefaultClasses() {
		String image_file = getSerializedImageFile();

		if (image_file != null) {
			if (!JmlLoader.loadSerializedImage(configuration, image_file)) {
				setError(
					"Could not load default classes from image:\n    "
						+ image_file
						+ "\nTry to regenerate the image from the Project Properties Dialog");
				return false;
			}
		} else {
			try {
				JmlLoader.loadDefaultClasses(configuration);
			} catch (jml2b.exceptions.InternalError e) {
				setError(
					"Could not load default classes\n"
						+ "Check that your JML search path is correct\n"
						+ e.getMessage());
				return false;
			}
		}

		return true;
	}

	/**
	 * Loads, links and type checks the given compilation units then call the coreRun
	 * method.
	 */
	public void run(IProgressMonitor monitor) {
		long time = System.currentTimeMillis();

		// Should never happen
		if (compilationUnits.size() == 0) {
			return;
		}

		// clear markers for the project (those markers are added when the
		// file cannot be found)
		try {
			project.deleteMarkers(
				PROBLEM_MARKER_TYPE,
				true,
				IResource.DEPTH_INFINITE);
		} catch (CoreException e) {
			monitor.done();
			setError("Error clearing markers: " + e.toString());
//			Package.clearAll();
			return;
		}

		monitor.beginTask(taskName, IProgressMonitor.UNKNOWN);

		// set the error handler
		ErrorHandler.setHandler(getErrorHandler());
		ErrorHandler.reset();

		// clears all the  loaded classes
//		Package.clearAll();

		monitor.subTask("Loading default classes");

		// load the default classes
		if (!loadDefaultClasses()) {
			monitor.done();
//			Package.clearAll();
			return;
		}

		if (monitor.isCanceled()) {
//			Package.clearAll();
			return;
		}

		// read and parse each file, and store them in the files vector
		// (vector of JmlFile elements)
		Vector files = new Vector();

		Vector lockedCI = new Vector();

		Iterator iterator = compilationUnits.iterator();

		IFolder output_folder = null;

		// current number of errors
		int file_count = 0;

		monitor.subTask("Loading files");

		try {
			// load and parse each compilation unit, storing the corresponding
			// destination folder.		
			while (iterator.hasNext()) {
				IResource cu = (IResource) iterator.next();
				//TODO A remettre
//				if (JackPlugin.isLock(cu)) {
//					continue;
//				}
				JackPlugin.lock(cu);
				lockedCI.add(cu);
				//				IResource source_resource = cu;
				IFolder tmp_folder = getAndCreateOutputDir();

				if (output_folder != null) {
					// ensures that it is the same output_folder as the previous one
					if (!output_folder.equals(tmp_folder)) {
						monitor.done();
						setError("JPO files can only be generated for one project at a time");
//						Package.clearAll();
						return;
					}
				} else {
					output_folder = tmp_folder;
				}

				// clear all the previous jack markers.
				try {
					cu.deleteMarkers(
						PROBLEM_MARKER_TYPE,
						true,
						IResource.DEPTH_INFINITE);
				} catch (CoreException e) {
					monitor.done();
					setError("Error clearing markers: " + e.toString());
//					Package.clearAll();
					return;
				}

				// load the file
				JmlFile file = loadFile(cu.getLocation(), javaProject);

				if (file != null) {
					// store the resource corresponding to the file in the jmlfile
					file.storeData(ECLIPSE_RESOURCE_KEY, cu);

					files.add(file);
					++file_count;
				}

				// check for cancel pressed
				if (monitor.isCanceled()) {
//					Package.clearAll();
					return;
				}
			}

			// stop here in case where errors have occured when loading the files.
			if (file_count != compilationUnits.size()
				|| ErrorHandler.getErrorCount() > 0) {
				// notify the monitor that the operation is finished
				monitor.done();
				setError("Error loading files");
//				Package.clearAll();
				return;
			}

			monitor.subTask("Linking files");

			// link the files
			for (int i = 0; i < files.size(); ++i) {
				JmlFile f = (JmlFile) files.get(i);
				try {
					f.link(configuration);
				} catch (ClassLoadException cle) {
					// the error is not displayed since it has already been.
				} catch (Jml2bException e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				}
				if (monitor.isCanceled()) {
//					Package.clearAll();
					return;
				}
			}

			if (ErrorHandler.getErrorCount() > 0) {
				monitor.done();
				setError("Error linking files");
//				Package.clearAll();
				return;
			}

			monitor.subTask("Linking methods body");

			// link statements from each of the loaded files.
			for (int i = 0; i < file_count; ++i) {
				JmlFile f = (JmlFile) files.get(i);
				try {
					f.linkStatements(configuration);
				} catch (Jml2bException e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				}

				if (monitor.isCanceled()) {
//					Package.clearAll();
					return;
				}
			}

			if (ErrorHandler.getErrorCount() > 0) {
				monitor.done();
				setError("Error linking statements");
//				Package.clearAll();
				return;
			}

			monitor.subTask("Type checking");

			// link statements from each of the loaded files.
			for (int i = 0; i < file_count; ++i) {
				JmlFile f = (JmlFile) files.get(i);
				try {
					f.typeCheck(configuration);
				} catch (Jml2bException e) {
					ErrorHandler.error(f, -1, -1, e.toString());
				}

				if (monitor.isCanceled()) {
//					Package.clearAll();
					return;
				}
			}

			if (ErrorHandler.getErrorCount() > 0) {
				monitor.done();
				setError("Type check error");
//				Package.clearAll();
				return;
			}

			monitor.subTask("Linking remaining files");
			// link the remaining files
			try {
				JmlLoader.linkStatements(configuration);
			} catch (Jml2bException e) {
				monitor.done();
				setError("Error linking remaining files : " + e.toString());
//				Package.clearAll();
				return;
			}

			if (ErrorHandler.getErrorCount() > 0) {
				monitor.done();
				setError("Error linking remaining files.");
//				Package.clearAll();
				return;
			}

			if (monitor.isCanceled()) {
//				Package.clearAll();
				return;
			}

			monitor.subTask("Generating JPO files");

			try {
				coreRun(monitor, file_count, files);
			} finally {
				// refresh the directory where proof obligations have been put (ensures
				// that eclipse stays in sync with the generated files).
				try {
					output_folder.refreshLocal(IResource.DEPTH_INFINITE, null);
				} catch (CoreException e) {
					setError(
						"Could not refresh Jack directory : " + e.toString());
				}

			}

		} finally {
			iterator = lockedCI.iterator();
			while (iterator.hasNext()) {
				IResource c = (IResource) iterator.next();
				JackPlugin.unLock(c);
			}
		}

		// notify the monitor that the operation is finished, and that the operation 
		// was not canceled.
		monitor.setCanceled(false);
		monitor.done();
		Logger.warn.println("   " + (System.currentTimeMillis() - time) + " ms");

	}

	/**
	 * This method is called when files are loaded and linked, it should perform the
	 * main action.
	 * @param monitor The current monitor
	 * @param file_count The number of JML file.
	 * @param files The set of JML file.
	 **/
	protected abstract void coreRun(
		IProgressMonitor monitor,
		int file_count,
		Vector files);

	/** 
	 * Return the folder corresponding to the proof obligations destination
	 * folder for the given compilation unit.
	 */
	private IFolder getAndCreateOutputDir() {
		IFolder po_dir = JackPlugin.getOutputDir(project);

		if (!po_dir.exists()) {
			try {
				// create the folder if it does not exists
				po_dir.create(false, true, null);
			} catch (CoreException e) {
				setError("Could not create Jack directory; " + e.toString());
				return null;
			}
		}
		return po_dir;
	}

	/** 
	 * Load and parse the given compilation unit.
	 */
	protected JmlFile loadFile(IPath path, IJavaProject p) {
		// get the path to the resource
		//IPath path = cu.getResource().getLocation();
		// convert this path to a File element
		File f = path.toFile();
		
		configuration.setProject(p);
//		JackJml2bConfiguration config = new JackJml2bConfiguration(p, Package.initPackage());

		JmlFile result = new JmlEntryFile(f).loadFile(configuration, false);

		if (result == null) {
			// handle errors and warnings from the parser.
			return null;
		}

		if (ErrorHandler.getErrorCount() > 0) {
			// if there where errors, return null
			return null;
		}

		int error_count = result.parse(configuration);
		if (error_count > 0) {
			return null;
		}

		return result;
	}
}
