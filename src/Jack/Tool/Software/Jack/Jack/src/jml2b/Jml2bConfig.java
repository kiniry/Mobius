//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Jml2bConfig.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b;

import java.io.File;
import java.util.Hashtable;
import java.util.Vector;

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
import jml2b.structure.statement.Expression;
import jml2b.util.JmlPathEntry;

import org.eclipse.swt.graphics.FontData;

/**
 * @author burdy
 */
public class Jml2bConfig implements IJml2bConfiguration {

	private File output_directory;

	private JmlPathEntry[] jmlPath;

	private boolean obviousPo;

	private Hashtable ht;
	
	private JavaLoader pack;
	
	private Type typeObject = null;
	
	private Class arrayClass = null;
	
	public IPackage getPackage() {
		return pack;
	}

	public void setPackage(JavaLoader pack) {
		this.pack = pack;
	}

	public Jml2bConfig(String[] path, boolean obvious) {
		jmlPath = JmlPathEntry.factory(path);
		obviousPo = obvious;
		ht = new Hashtable();
	}

	void setOutputDir(File output) {
		output_directory = output;
	}

	Jml2bConfig(String[] path) {
		output_directory = null;
		jmlPath = JmlPathEntry.factory(path);
		obviousPo = false;
	}

	public File getSubdirectory() {
		return output_directory;
	}

	public JmlPathEntry[] getJmlPath() {
		return jmlPath;
	}

	public String getRmiUrl() {
		return null;
	}

	public FontData getViewerFont() {
		return null;
	}

	public boolean isObviousPoGenerated() {
		return obviousPo;
	}

	public boolean isWellDefPoGenerated() {
		return true;
	}

	public boolean isViewShown(String name) {
		return false;
	}

//	public boolean isBViewShown() {
//		return false;
//	}
//
//	public boolean isSimplifyViewShown() {
//		return false;
//	}
//
//	public boolean isCoqViewShown() {
//		return false;
//	}

	public String getABProject() {
		return null;
	}

	public Expression getDefaultRequires() {
		return Expression.getTrue();
	}

	public ModifiesClause getDefaultModifies() {
		return new ModifiesEverything();
	}

	public Expression getDefaultEnsures() {
		return Expression.getTrue();
	}

	public Vector getDefaultExsures() {
		Vector res = new Vector();
		res
			.add(new Exsures(
				Type.createUnlinkedClass("java.lang.Exception"),
				null,
				Expression.getFalse()));
		return res;
	}

	public boolean isFileGenerated(String name) {
		return ((Boolean) ht.get(name)).booleanValue();
	}

	public void setFileGenerated(String name, boolean b) {
		ht.put(name, new Boolean(b));
	}


	public boolean isObviousProver(String name) {
		return false;
	}

//	public boolean isCoqFileGenerated() {
//		return true;
//	}
//
//	public boolean isSimplifyFileGenerated() {
//		return true;
//	}

//	/* (non-Javadoc)
//	 * @see jml2b.IJml2bConfiguration#getJmlPathAsClassPath()
//	 */
//	public String getJmlPathAsClassPath() {
//		String res = "";
//		String[] jmlP = getJmlPath();
//		boolean first = true;
//		for (int i = 0; i < jmlP.length; i++) {
//			if (first)
//				first = false;
//			else
//				res += ";";
//			res += jmlP[i];
//		}
//		return res;
//	}

	/* (non-Javadoc)
	 * @see jml2b.IJml2bConfiguration#getDefaultExternalFile()
	 */
	public boolean getDefaultExternalFile() {
		return true;
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
