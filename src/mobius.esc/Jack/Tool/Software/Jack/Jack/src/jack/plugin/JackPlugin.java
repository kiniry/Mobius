//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackPlugin.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/*******************************************************************************/
package jack.plugin;

import jack.plugin.compile.CompilationUnitDecorator;
import jack.util.Logger;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Enumeration;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

import jml2b.languages.Languages;
import jml2b.util.Util;
import jpov.Icons;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;


/**
 * Eclipse plugin for the <b>J</b>ava <b>A</b>pplet <b>C</b>orrectness <b>K</b>it.
 * @author A. Requet, L. Burdy
 */
public class JackPlugin extends AbstractUIPlugin {

	/**
	 * The shared instance.
	 */
	private static JackPlugin plugin;

	/**
	 * The resource bundle used by this plugin.
	 */
	private ResourceBundle resourceBundle;

	/** The default title that should be used for error and information dialogs. */
	public static final String DIALOG_TITLE = "Jack Plugin";

	// the preferences defined by this plugin
//	/**
//	 * Preference corresponding to the search path used when loading files.
//	 */
//	public static final String JMLPATH_PREFERENCE = "jackJmlPath";

	/** 
	 * Directory used to store the jpo files.
	 */
	public static final String JACK_SUBDIRECTORY = "jackJpoDir";

	/** Font used within the source viewer. */
	public static final String JACK_VIEWER_FONT = "jackViewerFont";

	public static final String MULTI_COMMENT_JML_COLOR = "multicommentjmlcolor";

	public static final String SINGLE_COMMENT_JML_COLOR =
		"singlecommentjmlcolor";

	public static final String JML_KEYWORD_COLOR = "jmlkeywordcolor";

	public static final String JACK_OBVIOUS_PO = "jackObviousPo";

	public static final String JACK_WELLDEF_LEMMA = "jackWellDefLemma";

	public static final String JACK_GENERATE = "jackGenerate";

	public static final String OBVIOUS_PROVER = "obviousProver";

	public static final String JACK_PROOF_TASK_MAX_RUNNING =
		"jackPoofTaskMaxRunning";

	/** 
	 * Boolean preference indicating wether a view should be 
	 * displayed. It is completed with the language name.
	 */
	public static final String JACK_VIEW_SHOW = "jackViewShow";

	public static final String PROVER_EXTENSION_ID = "jack.plugin.Prover";

	public static final QualifiedName JPO_FROM_CLASS = 
		new QualifiedName("jack.plugin", "jpofromclass");

	public static final QualifiedName ANNOTATED_CLASS =
		new QualifiedName("jack.plugin", "annotatedclass");

	public static final QualifiedName JACK_DIR_PROPERTY =
		new QualifiedName("jack.plugin", "jackdir");

	/** Name of the property corresponding to the image file used. */
	public static final QualifiedName SERIALIZED_IMAGE_PROPERTY =
		new QualifiedName("jack.plugin", "imagefile");

	/** Name of the property allowing the use of an image file. */
	public static final QualifiedName USE_SERIALIZED_IMAGE_PROPERTY =
		new QualifiedName("jack.plugin", "useimage");

	/** 
	 * Name of the property storing the roots used for generating the
	 * Serialized image.
	 */
	private static final QualifiedName SERIALIZED_IMAGE_ROOTS_PROPERTY =
		new QualifiedName("jack.plugin", "imageroots");

	/** 
	 * The path that is searched for JML files.
	 */
	private static final QualifiedName JMLPATH_PROPERTY =
		new QualifiedName("jack.plugin", "jmlpath");
	
	private static final QualifiedName JMLPATH_USE_DEFAULT_CLASSPATH_PROPERTY =
		new QualifiedName("jack.plugin", "jmlpathusedefaultclasspath");
	/** 
	 * The property corresponding to the fact that a file is compiled or not.
	 */
	public static final QualifiedName JML_COMPILED =
		new QualifiedName("jack.plugin", "jmlcompiled");

	public static final QualifiedName JML_BYTECODE_COMPILED =
		new QualifiedName("jack.plugin", "jmlbytecodecompiled");

	public static final QualifiedName LOCK =
		new QualifiedName("jack.plugin", "lock");

	/** 
	 * The property corresponding to the depends file.
	 */
	public static final QualifiedName DEPENDS =
		new QualifiedName("jack.plugin", "depends");

	/** 
	 * The Id corresponding to the Jack PO Viewer view. 
	 */
	public static final String JACK_VIEW_ID = "jack.plugin.poview";

	/**
	 * The Id corresponding to the Jack Prover view.
	 */
	public static final String JACK_PROOF_VIEW_ID = "jack.plugin.proofview";

	public static final String JACK_PERSPECTIVE_ID =
		"jack.plugin.perspective.JackPerspective";

	/**
	 * The Id corresponding to the Jack Metrics view.
	 */
	public static final String JACK_METRICS_VIEW_ID = "jack.plugin.metricsview";

	/**
	 * The Id corresponding to 
	 */
	public static final String SOURCE_CASE_VIEWER_ID =
		"jack.plugin.perspective.SourceCaseViewer";

	/**
	 * The Id corresponding to 
	 */
	public static final String CASE_EXPLORER_VIEW_ID =
		"jack.plugin.perspective.CaseExplorer";

	/**
	 * The Id corresponding to 
	 */
	public static final String LEMMA_VIEWER =
		"jack.plugin.perspective.LemmaViewer";

	/** 
	 * Name of the serialized image file. This file is located in the 
	 * jack subdirectory.
	 */
	public static final String IMAGE_NAME = "classes.bin";

	public static final String ALWAYS_SAVE_BEFORE_EDITING =
		"always_save_before_editing";

	public static final String ALWAYS_SAVE_BEFORE_COMPILING =
		"always_save_before_compiling";

	public static final String ALWAYS_SAVE_BEFORE_PROVING =
		"always_save_before_proving";

	public static final String ALWAYS_COMPILE_BEFORE_EDITING =
		"always_compile_before_editing";

	public static final String ALWAYS_COMPILE_BEFORE_PROVING =
		"always_compile_before_proving";

	public static void unJmlCompile(IResource r) throws CoreException {
		r.setPersistentProperty(JackPlugin.JML_COMPILED, "false");
		r.setPersistentProperty(JackPlugin.JML_BYTECODE_COMPILED, "false");
		CompilationUnitDecorator.refresh(r);
		String depends = r.getPersistentProperty(JackPlugin.DEPENDS);
		if (depends != null) {
			String[] tok = jml2b.util.Util.tokenize(depends, ";");
			for (int i = 0; i < tok.length; i++) {
				IResource dependR = JpovUtil.getResource(tok[i]);
				if (dependR != null
					&& dependR.getPersistentProperty(
						JackPlugin.JML_COMPILED).equals(
						"true"))
					unJmlCompile(dependR);
			}
		}
	}

	public static synchronized void lock(IResource cu) {
		try {
			cu.setPersistentProperty(JackPlugin.LOCK, "true");
		} catch (CoreException ce) {
		}
	}

	public static synchronized void unLock(IResource cu) {
		try {
			cu.setPersistentProperty(JackPlugin.LOCK, "false");
		} catch (CoreException ce) {
		}
	}

	public static synchronized boolean isLock(IResource cu) {
		try {
			return cu.getPersistentProperty(JackPlugin.LOCK) != null
				&& cu.getPersistentProperty(JackPlugin.LOCK).equals("true");
		} catch (CoreException ce) {
			return true;
		}
	}

	/**
	 * The constructor.
	 */
	public JackPlugin() {
		plugin = this;
		try {
			resourceBundle =
				ResourceBundle.getBundle("jack.pog.PogPluginResources");
		} catch (MissingResourceException x) {
			resourceBundle = null;
		}
		//Icons.initImages(getIconDir());
		// set defaults for preferences

	}

	/**
	 * Returns the shared instance.
	 */
	public static JackPlugin getDefault() {
		return plugin;
	}

	/**
	 * Returns the workspace instance.
	 */
	public static IWorkspace getWorkspace() {
		return ResourcesPlugin.getWorkspace();
	}

	/**
	 * Returns the string from the plugin's resource bundle,
	 * or 'key' if not found.
	 */
	public static String getResourceString(String key) {
		ResourceBundle bundle = JackPlugin.getDefault().getResourceBundle();
		try {
			return bundle.getString(key);
		} catch (MissingResourceException e) {
			return key;
		}
	}

	
	public void start(BundleContext context) throws Exception {
		super.start(context);
		Icons.initImages(getIconDir());
		IPreferenceStore store = getPreferenceStore();
//		store.setDefault(JMLPATH_PREFERENCE, "");
		store.setDefault(JackPlugin.JACK_SUBDIRECTORY, "JPOs");
		store.setDefault(JackPlugin.JACK_PROOF_TASK_MAX_RUNNING, 3);
		store.setDefault(JackPlugin.JACK_OBVIOUS_PO, false);
		store.setDefault(JackPlugin.JACK_WELLDEF_LEMMA, false);
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			store.setDefault(JackPlugin.JACK_GENERATE + name, false);
			store.setDefault(JackPlugin.OBVIOUS_PROVER + name, false);
			store.setDefault(JackPlugin.JACK_VIEW_SHOW + name, true);
		}

		PreferenceConverter.setDefault(
				store,
				JackPlugin.JACK_VIEWER_FONT,
				PreferenceConverter.FONTDATA_DEFAULT_DEFAULT);

		IResourceChangeListener listener = new MyResourceChangeReporter();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(
					listener,
					IResourceChangeEvent.POST_CHANGE);
	}
	
	/**
	 * Return the property property_name for the given resource. 
	 * If the property is not defined for this resource, return
	 * the value of the preference preference_name.
	 */
	public String getProperty(
		IResource resource,
		QualifiedName property_name,
		String preference_name) {
		try {
			String result = resource.getPersistentProperty(property_name);
			if (result == null) {
				return getPreferenceStore().getString(preference_name);
			}

			return result;
		} catch (CoreException e) {
			Logger.err.println("Exception catched: " + e.toString());
			return getPreferenceStore().getString(preference_name);
		}
	}

	/**
	 * Returns the plugin's resource bundle,
	 */
	public ResourceBundle getResourceBundle() {
		return resourceBundle;
	}

	//	/**
	//	 * Returns the default Jml path. That is, the Jml path that is set
	//	 * in the properties dialog.
	//	 */
	//	public static String getDefaultJmlPath() {
	//		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
	//		return prefs.getString(JackPlugin.JMLPATH_PREFERENCE);
	//	}

	/**
	 * Returns the default output directory. That is, the directory that
	 * is set in the properties dialog.
	 */
	public static String getDefaultOutputDir() {
		// get the output directory
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		String output_dir = prefs.getString(JackPlugin.JACK_SUBDIRECTORY);

		return output_dir;
	}

	/**
	 * Returns the Jml search path preference.
	 */
	public static String[] getJmlPath(IJavaProject project) {
		if (isDefaultClassPathUsed(project.getProject()))
			return getDefaultJmlPath(project);
		else {
			try {
				String s =
					project.getProject().getPersistentProperty( JMLPATH_PROPERTY);
				if (s.indexOf(project.getProject().getLocation().toString()) == -1)
					s = project.getProject().getLocation() + File.pathSeparator + s;
				return Util.tokenize(s, File.pathSeparator);
			}
			catch (CoreException ce) {
				return new String[0];
			}
		}
	}
	
	public static String[] getDefaultJmlPath(IJavaProject project) {
		try {
			IClasspathEntry[] icpea =  project.getResolvedClasspath(false);
			String[] res = new String[icpea.length];
			for (int i=0; i < icpea.length; i++) {
				switch (icpea[i].getEntryKind()) {
					case IClasspathEntry.CPE_SOURCE : {
						//IProject proj = project.getProject();
						
						res[i] = project.getProject().getParent().getLocation().toOSString();
						res[i] += icpea[i].getPath().toString();
						break;
					}
					
					case IClasspathEntry.CPE_LIBRARY :
						res[i] = icpea[i].getPath().toString();
						break;
				}
			}
			return res;
		}
		catch (JavaModelException jme) {
			return new String[0];
		}
	}

	public static boolean isDefaultClassPathUsed(IProject project) {
		try {
			String s = project.getPersistentProperty(
													JMLPATH_USE_DEFAULT_CLASSPATH_PROPERTY);
		return
			s == null || s.equals("true");
		}
		catch (CoreException ce) {
			return false;
		}
	}
				
	
	/**
	 * Sets the jml search path for the given project.
	 */
	public static void setJmlPath(IProject project, boolean useDefaultClassPath, String[] new_path)
		throws CoreException {
		project.setPersistentProperty(
										JMLPATH_USE_DEFAULT_CLASSPATH_PROPERTY,
										useDefaultClassPath ? "true" : "false");
	project.setPersistentProperty(
			JMLPATH_PROPERTY,
			Util.untokenize(new_path, File.pathSeparator));
	}

	/**
	 * Returns the ouput directory for the given project. Note that this 
	 * directory is not created if it does not exists yet.
	 */
	public static IFolder getOutputDir(IProject project) {
		return project.getFolder(getJpoSubdirectory(project));
	}

	/**
	 * Returns the boolean indicating obvious goal generation.
	 */
	public static boolean getObviousPoGeneration() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return prefs.getBoolean(JACK_OBVIOUS_PO);
	}

	public static boolean getWellDefPoGeneration() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return prefs.getBoolean(JACK_WELLDEF_LEMMA);
	}

	public static boolean getFileGeneration(String name) {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return !prefs.contains(JACK_GENERATE + name) || prefs.getBoolean(JACK_GENERATE + name);
	}

	public static boolean isObviousProver(String name) {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return prefs.getBoolean(OBVIOUS_PROVER + name);
	}

	/**
	 * Returns the integer indicating the maximum number of running proof tasks.
	 */
	public static int getMaxProofRunning() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return prefs.getInt(JACK_PROOF_TASK_MAX_RUNNING);
	}

	public static RGB getMultiCommentJmlColor() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return PreferenceConverter.getColor(prefs, MULTI_COMMENT_JML_COLOR);
	}

	public static RGB getSingleCommentJmlColor() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return PreferenceConverter.getColor(prefs, SINGLE_COMMENT_JML_COLOR);
	}

	public static RGB getJmlKeywordColor() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return PreferenceConverter.getColor(prefs, JML_KEYWORD_COLOR);
	}

	/**
	 * Returns the list of fully qualifed class name corresponding to 
	 * the additional roots used for generating the serialized image.
	 * 
	 * Return an array with zero size if the roots are empty.
	 */
	public static String[] getSerializedImageRoots(IProject project)
		throws CoreException {
		String property_content;
		property_content =
			project.getPersistentProperty(SERIALIZED_IMAGE_ROOTS_PROPERTY);
		if (property_content == null) {
			return new String[0];
		}
		if (property_content.equals("")) {
			return new String[0];
		}

		return Util.tokenize(property_content, "|");
	}

	/**
	 * Sets the list of additional roots used for generating the serialized
	 * image.
	 */
	public static void setSerializedImageRoots(
		IProject project,
		String[] classes)
		throws CoreException {
		String tokenized = Util.untokenize(classes, "|");
		project.setPersistentProperty(
			SERIALIZED_IMAGE_ROOTS_PROPERTY,
			tokenized);
	}

	/**
	 * 
	 * Returns the directory where the icons are stored.
	 */
	public static URL getIconDir() {
		try {
			URL install_url =
					JackPlugin.getDefault().getBundle().getEntry("/");
			//Logger.get().println(install_url);
			//getDescriptor().getInstallURL();
			return new URL(install_url, "imgs/icons/");
		} catch (MalformedURLException e) {
			return null;
		}
	}

	/**
	 * Returns the jpo file corresponding to the given compilation unit.
	 * Returns null if no jpo file could be found.
	 * <p>
	 * Note that this method needs to be updated if 
	 * <code>JmlFile.getFlatName</code> is modified.
	 */
	public static IFile getJpoFile(ICompilationUnit compilation_unit) {
		IFile java_file = (IFile) compilation_unit.getResource();

		// get the project corresponding to the java file.
		IProject project = java_file.getProject();
		String folder_string = getJpoSubdirectory(project);
		IFolder jpo_folder = project.getFolder(folder_string);

		if (jpo_folder == null) {
			return null;
		}

		String file_name = getJavaPrefix(java_file);

		IPackageDeclaration[] pkg;
		try {
			pkg = compilation_unit.getPackageDeclarations();
		} catch (JavaModelException e) {
			Logger.err.println(
				"JackPlugin.getJpoFile: JavaModelException catched: "
					+ e.toString());
			return null;
		}

		// name of the jpo file
		String jpo_name;

		if (pkg == null || pkg.length == 0) {
			jpo_name = file_name + ".jpo";
		} else {
			if (pkg.length != 1) {
				// error
				return null;
			}
			String pkg_name = pkg[0].getElementName();
			jpo_name = pkg_name.replace('.', '_') + "_" + file_name + ".jpo";
		}
		IFile jpo_file = jpo_folder.getFile(jpo_name);

		// check that the file exists
		if (!jpo_file.exists()) {
			return null;
		}
		return jpo_file;
	}

	/**
	 * Returns the bytecode jpo file corresponding to the given compilation unit.
	 * Returns null if no jpo file could be found.
	 */
	public static IFile getBytecodeJpoFile(ICompilationUnit c) {
		try {
			String jpo = c.getResource().getPersistentProperty(JackPlugin.JPO_FROM_CLASS);
			IFile java_file = (IFile) c.getResource();
			
			// get the project corresponding to the java file.
			IProject project = java_file.getProject();
			String folder_string = JackPlugin.getJpoSubdirectory(project);
			IFolder jpo_folder = project.getFolder(folder_string);
			
			if (jpo_folder == null) {
				return null;
			}
			return jpo_folder.getFile(jpo + ".jpo");
		}
		catch (CoreException ce) {
			return null;
		}
	}

	/**
	 * Return the Jpo folder corresponding to the given project. The returned
	 * path string correspond to the name of the subdirectory where 
	 * <code>.jpo</code> files are stored.
	 * <p>
	 * It should be added to the project directory in order to obtain the
	 * path where files are written.  
	 */
	public static String getJpoSubdirectory(IProject project) {
		String result;

		try {
			// look for the property
			result =
				project.getPersistentProperty(JackPlugin.JACK_DIR_PROPERTY);
			if (result != null) {
				return result;
			}
		} catch (CoreException e) {
		}

		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		result = prefs.getString(JackPlugin.JACK_SUBDIRECTORY);
		return result;
	}

	/**
	 * return the name of a .java file without its extension.
	 * 
	 * Assumes that the extension is 4 characters long.
	 */
	private static String getJavaPrefix(IFile f) {
		String name = f.getName();
		return name.substring(0, name.length() - 5);
	}

	public static FontData getViewerFont() {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return PreferenceConverter.getFontData(
			prefs,
			JackPlugin.JACK_VIEWER_FONT);
	}

}

/**
 * This class implements a resource change listener. It allows to update decorators 
 * when a compiled file is changed.
 *
 *  @author L. Burdy
 **/
class MyResourceChangeReporter implements IResourceChangeListener {

	public void resourceChanged(IResourceChangeEvent event) {
		try {
			switch (event.getType()) {
				case IResourceChangeEvent.PRE_CLOSE :
					break;
				case IResourceChangeEvent.PRE_DELETE :
					break;
				case IResourceChangeEvent.POST_CHANGE :
					event.getDelta().accept(new DeltaPrinter());
					break;
				case IResourceChangeEvent.PRE_BUILD :
					event.getDelta().accept(new DeltaPrinter());
					break;
				case IResourceChangeEvent.POST_BUILD :
					event.getDelta().accept(new DeltaPrinter());
					break;
			}
		} catch (CoreException ce) {
			// it seems like a normal behavior not to find some resources
			Logger.warn.println(ce.getMessage());
			//ce.printStackTrace();
		}
	}

}

/**
 * This class implements a resource delta visitor. It allows to update decorators 
 * when a compiled file is changed.
 *
 *  @author L. Burdy
 **/
class DeltaPrinter implements IResourceDeltaVisitor {

	/**
	 * Sets the JML_COMPILED property to false to a changed ressource and to its
	 * dependees.
	 **/
	public boolean visit(IResourceDelta delta) throws CoreException {
		IResource res = delta.getResource();
		switch (delta.getKind()) {
			case IResourceDelta.ADDED :
				break;
			case IResourceDelta.REMOVED :
				break;
			case IResourceDelta.CHANGED :
				if (delta.getMarkerDeltas().length > 0)
					break;
				JackPlugin.unJmlCompile(res);
				break;
		}
		return true; // visit the children
	}

}
