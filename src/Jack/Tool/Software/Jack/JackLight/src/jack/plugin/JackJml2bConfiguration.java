//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackJml2bConfiguration.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin;

import java.io.File;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ClassLoadException;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.IPackage;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.ModFlags;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.jml.ModifiesEverything;
import jml2b.structure.jml.ModifiesNothing;
import jml2b.structure.statement.Expression;
import jml2b.util.JmlPathEntry;
import jml2b.util.Util;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.graphics.FontData;

/**
 * This class represents a configuration extracted from the Jack plugin and used
 * to compile, edit and prove jml files.
 * 
 * @author A. Requet, L. Burdy
 **/
public class JackJml2bConfiguration implements IJml2bConfiguration {
	private boolean defaultExternalFile = true;

	private IJavaProject javaProject;
	private IProject project;

	private Vector defaultExsures;
	private Expression defaultEnsures;
	private Expression defaultRequires;
	private ModifiesClause defaultModifies;

	/**
	 * Instance corresponding to the <code>java.lang.Object</code> type.
	 */
	private Type typeObject = null;

	/**
	 * The class that represents arrays.
	 **/
	private Class arrayClass = null;

	private JavaLoader pack;
	/**
	 * Creates a new JackJml2bConfiguration suitable for use with
	 * the given project.
	 * 
	 * @param prj the project this configuration corresponds to.
	 */
	public JackJml2bConfiguration(IJavaProject prj, JavaLoader p) {
		project = prj.getProject();
		javaProject = prj;
		pack = p;
		typeObject = null;
	}

	public JackJml2bConfiguration(IProject prj, JavaLoader p) {
		project = prj;
		pack = p;
		typeObject = null;
	}

	public File getSubdirectory() {
		IPath path = JackPlugin.getOutputDir(project).getLocation();
		return path.toFile();
	}

	public JmlPathEntry[] getJmlPath() {
		return JmlPathEntry.factory(JackPlugin.getJmlPath(javaProject));
	}

	//	public String getJmlPathAsClassPath() {
	//		String res = "";
	//		String[] jmlP = getJmlPath();
	//		boolean first = true;
	//		for (int i = 0; i < jmlP.length; i++) {
	//			if (first)
	//				first = false;
	//			else
	//				res += ":";
	//			res += jmlP[i];
	//		}
	//		return res;
	//	}
	//

	public FontData getViewerFont() {
		return JackPlugin.getViewerFont();
	}

	public boolean isObviousPoGenerated() {
		return JackPlugin.getObviousPoGeneration();
	}

	public boolean isWellDefPoGenerated() {
		return JackPlugin.getWellDefPoGeneration();
	}

	public boolean isFileGenerated(String name) {
		return JackPlugin.getFileGeneration(name);
	}

	public void setFileGenerated(String name, boolean b) {
	}

	public boolean isObviousProver(String name) {
		return JackPlugin.isObviousProver(name);
	}

	public boolean isViewShown(String name) {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();

		return prefs.getBoolean(JackPlugin.JACK_VIEW_SHOW + name);
	}

	public Expression getDefaultRequires() {
		if (defaultRequires == null) {
			if (isDefaultJmlRequiresTrue(project.getProject())) {
				defaultRequires = Expression.getTrue();
			} else {
				String s = getDefaultJmlRequiresText(project.getProject());
				if (s == null) {
					defaultRequires = Expression.getTrue();
				}
				try {
					defaultRequires = Expression.getFromString(s);
				} catch (Jml2bException e) {
					// should never happen
					defaultRequires = Expression.getTrue();
				}
			}
		}
		return defaultRequires;
	}

	public ModifiesClause getDefaultModifies() {
		if (defaultModifies == null) {
			String tmp = getDefaultJmlModifies(project.getProject());
			if (tmp.equals(NOTHING)) {
				defaultModifies = new ModifiesNothing();
			} else {
				defaultModifies = new ModifiesEverything();
			}
		}
		return defaultModifies;
	}

	public Expression getDefaultEnsures() {
		if (defaultEnsures == null) {
			if (isDefaultJmlEnsuresTrue(project.getProject())) {
				defaultEnsures = Expression.getTrue();
			} else {
				String s = getDefaultJmlEnsuresText(project.getProject());
				if (s == null) {
					defaultEnsures = Expression.getTrue();
				}
				try {
					defaultEnsures = Expression.getFromString(s);
				} catch (Jml2bException e) {
					// should never happen
					defaultEnsures = Expression.getTrue();
				}
			}
		}
		return defaultEnsures;
	}

	public Vector getDefaultExsures() {
		if (defaultExsures == null) {

			defaultExsures = new Vector();

			switch (getDefaultJmlExsuresType(project.getProject())) {
				case EXSURES_OTHER :
					{
						try {
							Exsures.getExsures(
								getDefaultJmlExsuresOther(project.getProject()),
								defaultExsures);
							break;
						} catch (Jml2bException e) {
							// FALL THROUGH
							// in that case, we are falling in the deafult case
							// that correspond to a safe choice (should never
							// happen)						
						}
					}
				default :
				case EXSURES_EXCEPTION_FALSE :
					defaultExsures.add(
						new Exsures(
							Type.createUnlinkedClass("java.lang.Exception"),
							null,
							Expression.getFalse()));
					break;
				case EXSURES_EXCEPTION_TRUE :
					defaultExsures.add(
						new Exsures(
							Type.createUnlinkedClass("java.lang.Exception"),
							null,
							Expression.getTrue()));
					break;
				case EXSURES_RUNTIMEEXCEPTION_FALSE :
					{
						String[] exceptions =
							getDefaultJmlExsuresExceptions(project.getProject());
						for (int i = 0; i < exceptions.length; ++i) {
							Exsures tmp;
							tmp =
								new Exsures(
									Type.createUnlinkedClass(exceptions[i]),
									null,
									Expression.getFalse());
							defaultExsures.add(tmp);
						}
						break;
					}
			}
		}
		return defaultExsures;
	}

	private static void setBooleanProperty(
		IResource resource,
		QualifiedName q,
		boolean value)
		throws CoreException {
		resource.setPersistentProperty(q, value ? "true" : "false");
	}

	/**
	 * Indicate wether the default value for <code>requires</code> clauses is 
	 * set to <code>requires true</code> or not.
	 * In the case where it is not set to <code>requires true</code>, then
	 * the content of the clause is given by the 
	 * <code>getDefaultJmlRequiresText</code> method.
	 *
	 * @see JackPlugin#getDefaultJmlRequiresText(IProject)
	 *   
	 * @param project the project whose property should be returned.
	 * @return boolean true if the default value for requires clauses is
	 *     <code>true</code>, false if a special value is given.
	 */
	public static boolean isDefaultJmlRequiresTrue(IProject project) {
		try {
			return getBooleanProperty(
				project,
				JackJml2bConfiguration.JML_REQUIRES_TRUE_PROPERTY);
		} catch (CoreException e) {
			return true;
		}
	}

	public static boolean setDefaultJmlRequiresTrue(
		IProject project,
		boolean value) {
		try {
			boolean res =
				value
					!= getBooleanProperty(
						project,
						JackJml2bConfiguration.JML_REQUIRES_TRUE_PROPERTY);
			setBooleanProperty(
				project,
				JackJml2bConfiguration.JML_REQUIRES_TRUE_PROPERTY,
				value);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	public static boolean isDefaultJmlEnsuresTrue(IProject project) {
		try {
			return getBooleanProperty(
				project,
				JackJml2bConfiguration.JML_ENSURES_TRUE_PROPERTY);
		} catch (CoreException e) {
			return true;
		}
	}

	public static boolean setDefaultJmlEnsuresTrue(
		IProject project,
		boolean value) {
		try {
			boolean res =
				value
					!= getBooleanProperty(
						project,
						JackJml2bConfiguration.JML_ENSURES_TRUE_PROPERTY);
			setBooleanProperty(
				project,
				JackJml2bConfiguration.JML_ENSURES_TRUE_PROPERTY,
				value);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	public static boolean setDefaultJmlRequiresText(
		IProject project,
		String value) {
		try {
			boolean res =
				!value.equals(
					project.getPersistentProperty(
						JML_DEFAULT_REQUIRES_TEXT_PROPERTY));
			project.setPersistentProperty(
				JackJml2bConfiguration.JML_DEFAULT_REQUIRES_TEXT_PROPERTY,
				value);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	public static boolean setDefaultJmlEnsuresText(
		IProject project,
		String value) {
		try {
			boolean res =
				!value.equals(
					project.getPersistentProperty(
						JackJml2bConfiguration
							.JML_DEFAULT_ENSURES_TEXT_PROPERTY));
			project.setPersistentProperty(
				JackJml2bConfiguration.JML_DEFAULT_ENSURES_TEXT_PROPERTY,
				value);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	/**
	 * 
	 * @param project
	 * @param exceptions an array containing the fully qualifed name of the 
	 *         exceptions.
	 */
	public static boolean setDefaultJmlExsuresExceptions(
		IProject project,
		String[] exceptions) {
		String encoded = Util.untokenize(exceptions, "|");
		try {
			boolean res =
				!encoded.equals(
					project.getPersistentProperty(
						JML_DEFAULT_EXSURES_RUNTIMEEXCEPTIONS_PROPERTY));
			project.setPersistentProperty(
				JackJml2bConfiguration
					.JML_DEFAULT_EXSURES_RUNTIMEEXCEPTIONS_PROPERTY,
				encoded);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	public static boolean setDefaultJmlModifies(
		IProject project,
		String value) {
		try {
			boolean res =
				!value.equals(
					project.getPersistentProperty(
						JackJml2bConfiguration.JML_DEFAULT_MODIFIES_PROPERTY));
			project.setPersistentProperty(
				JackJml2bConfiguration.JML_DEFAULT_MODIFIES_PROPERTY,
				value);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	private static boolean getBooleanProperty(
		IResource resource,
		QualifiedName q)
		throws CoreException {
		String str = resource.getPersistentProperty(q);
		if (str != null && str.equals("false")) {
			return false;
		}
		return true;
	}

	/**
	 * Returns the default requires clause for jml if it is not set to 
	 * requires true.
	 *  
	 * @param project the project whose property should be returned
	 * @return the content of the default requires clause as a string.
	 *          null if an error occured or if the property is not set.
	 */
	public static String getDefaultJmlRequiresText(IProject project) {
		try {
			return project.getPersistentProperty(
				JackJml2bConfiguration.JML_DEFAULT_REQUIRES_TEXT_PROPERTY);
		} catch (CoreException e) {
			return null;
		}
	}

	/**
	 * Returns the default ensures clause for jml.
	 *  
	 * @param project the project whose property should be returned
	 * @return the content of the default requires clause as a string.
	 *          null if an error occured or if the property is not set.
	 */
	public static String getDefaultJmlEnsuresText(IProject project) {
		try {
			return project.getPersistentProperty(
				JackJml2bConfiguration.JML_DEFAULT_ENSURES_TEXT_PROPERTY);
		} catch (CoreException e) {
			return null;
		}
	}

	/**
	 * Return the default exsures type for the given project.
	 * 
	 * @param project
	 */
	public static int getDefaultJmlExsuresType(IProject project) {
		String s;
		try {
			s =
				project.getPersistentProperty(
					JML_DEFAULT_EXSURES_TYPE_PROPERTY);
		} catch (CoreException e) {
			return EXSURES_EXCEPTION_FALSE;
		}
		if (s == null) {
			return EXSURES_EXCEPTION_FALSE;
		}
		return Integer.parseInt(s);
	}

	public static boolean setDefaultJmlExsuresType(
		IProject project,
		int value) {
		try {
			boolean res =
				!new Integer(value).equals(
					project.getPersistentProperty(
						JML_DEFAULT_EXSURES_TYPE_PROPERTY));
			project.setPersistentProperty(
				JML_DEFAULT_EXSURES_TYPE_PROPERTY,
				Integer.toString(value));
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	public static String getDefaultJmlExsuresOther(IProject project) {
		try {
			return project.getPersistentProperty(
				JML_DEFAULT_EXSURES_OTHER_PROPERTY);
		} catch (CoreException e) {
			return null;
		}
	}

	public static boolean setDefaultJmlExsuresOther(
		IProject project,
		String value) {
		try {
			boolean res =
				!value.equals(
					project.getPersistentProperty(
						JML_DEFAULT_EXSURES_OTHER_PROPERTY));
			project.setPersistentProperty(
				JML_DEFAULT_EXSURES_OTHER_PROPERTY,
				value);
			return res;
		} catch (CoreException e) {
			return true;
		}
	}

	/*@
	  @ ensures \result != null;
	  @*/
	public static String[] getDefaultJmlExsuresExceptions(IProject project) {
		String s;
		try {
			s =
				project.getPersistentProperty(
					JackJml2bConfiguration
						.JML_DEFAULT_EXSURES_RUNTIMEEXCEPTIONS_PROPERTY);
			return s != null ? Util.tokenize(s, "|") : new String[0];
		} catch (CoreException e) {
			return new String[0];
		}
	}

	/**
	 * Returns the default modifies clause for jml specifications.
	 * 
	 * @param project the project for which the default is set.
	 * @return String the value for modifies clauses that should be used when no
	 *      specification is given.
	 */
	/*@ 
	  @ ensures \result != null;
	  @*/
	public static String getDefaultJmlModifies(IProject project) {
		try {
			String result =
				project.getPersistentProperty(
					JackJml2bConfiguration.JML_DEFAULT_MODIFIES_PROPERTY);
			return result != null ? result : EVERYTHING;
		} catch (CoreException e) {
			return EVERYTHING;
		}
	}

	private static final QualifiedName JML_DEFAULT_ENSURES_TEXT_PROPERTY =
		new QualifiedName("jack.plugin", "jmldefaultensures");

	private static final QualifiedName JML_REQUIRES_TRUE_PROPERTY =
		new QualifiedName("jack.plugin", "jmlrequirestrue");

	private static final QualifiedName JML_DEFAULT_REQUIRES_TEXT_PROPERTY =
		new QualifiedName("jack.plugin", "jmldefaultrequires");

	private static final QualifiedName JML_ENSURES_TRUE_PROPERTY =
		new QualifiedName("jack.plugin", "jmlensurestrue");

	private static final QualifiedName JML_DEFAULT_EXSURES_TYPE_PROPERTY =
		new QualifiedName("jack.plugin", "jmlexsurestype");

	private static final QualifiedName JML_DEFAULT_EXSURES_RUNTIMEEXCEPTIONS_PROPERTY =
		new QualifiedName("jack.plugin", "jmldefaultexceptions");

	private static final QualifiedName JML_DEFAULT_EXSURES_OTHER_PROPERTY =
		new QualifiedName("jack.plugin", "jmldefaultexsuresother");

	private static final QualifiedName JML_DEFAULT_MODIFIES_PROPERTY =
		new QualifiedName("jack.plugin", "jmldefaultmodifies");

	public static final int EXSURES_EXCEPTION_FALSE = 0;
	public static final int EXSURES_EXCEPTION_TRUE = 1;
	public static final int EXSURES_RUNTIMEEXCEPTION_FALSE = 2;
	public static final int EXSURES_OTHER = 3;

	public static final String EVERYTHING = "\\everything";

	public static final String NOTHING = "\\nothing";

	public boolean getDefaultExternalFile() {
		return defaultExternalFile;
	}

	/**
	 * @param b
	 */
	public void setDefaultExternalFile(boolean b) {
		defaultExternalFile = b;
	}

	public IPackage getPackage() {
		return pack;
	}

	public void setProject(IJavaProject p) {
		javaProject = p;
		project = p.getProject();
	}

	/**
	 * Returns a type corresponding to the <code>java.lang.Object</code>
	 * class.
	 * 
	 * @param config the configuration that should be used for loading
	 *     classes.
	 * @return Type the type representing the <code>java.lang.Object</code>
	 *     class.
	 */
	public Type getObject()
		throws Jml2bException {
		//		try {
		if (typeObject == null) {
//			if (config == null) {
//				throw new InternalError("Type.getObject: config is null while loading java.lang.Object");
//			}
			AClass object =
				pack.getJavaLang().getAndLoadClass(this, "Object");
			if (object == null) {
				throw new ClassLoadException("Cannot load class java.lang.Object");
			}
			typeObject = new Type(object);
		}
		//		} catch (Jml2bException e) {
		//			throw new InternalError(
		//				"Cannot load class java.lang.Object (catched "
		//					+ e.toString()
		//					+ ")");
		//		}

		return typeObject;
	}

	/**
	 * Return the class that is used to represent arrays. This class currently 
	 * does not belong to any package 
	 */
	public Class getArray()
		throws Jml2bException {
		if (arrayClass == null) {
			arrayClass = new Class(null, null, null, null, true);

			// set the superclass to Object
			arrayClass.setSuperClass(getObject());

			// add the length field.
			Field f =
				new Field(
					new ParsedItem(),
					new Modifiers(ModFlags.PUBLIC),
					Type.getInteger(),
					"length",
					null);
			f.setDefiningClass(arrayClass);
			f.nameIndex = 0;
			arrayClass.fields.add(f);

			// set the name of the class
			arrayClass.setName("[");
		}
		return arrayClass;
	}


}
