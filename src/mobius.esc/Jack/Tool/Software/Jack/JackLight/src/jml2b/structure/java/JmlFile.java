//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JmlFile.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.java;

import java.io.File;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Map;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.ParseException;
import jml2b.link.LinkContext;
import jml2b.structure.IPackage;
import jml2b.util.JmlEntryFile;
import jml2b.util.JmlFileEntry;
import antlr.collections.AST;

/** 
 * Class keeping information on Java/JML files.
 * It basically contains a set of classes.
 * @author L. Burdy, A. Requet
 */
public class JmlFile implements Serializable, IJmlFile {

	protected transient AST fileAST;

	/** 
	 * FileName of the corresponding file (if any)
	 */
	public JmlFileEntry fileName;

	/** 
	 * Vector containing the different classes defined in this file.
	 * All the elements stored are of type Class.
	 */
	private Vector classes;

	/** 
	 * Vector containing the imported packages. That is, the packages P.
	 * imported as import P.*;
	 */
	// @ invariant \elemtype(\typeof(importedPackages.elementData)) == \type(Package);
	protected Vector importedPackages;

	/** 
	 * Vector containing the classes imported from other packages.
	 * It maps String (corresponding to the short name of the class
	 * to Package)
	 */
	Map importedClasses;

	/** 
	 * Package this files belongs to. It is set to root if the package is 
	 * unnamed.
	 */
	protected Package filePackage;

	/**
	 * Set of files name from witch this jml file depends.
	 */
	Vector depends;

	String[] langNames;

	/**
	 * Map allowing users of JmlFiles to store information that they want to 
	 * retrieve later.
	 * <p>
	 * It is currently used by the eclipse plugin to store the eclipse resource 
	 * corresponding to the file in order to display error messages.
	 * <p>
	 * In order to reduce the overhead, the map object is only created when
	 */
	private transient Map userData;

	private transient IJml2bConfiguration config;

	/** 
	 * Store the data using key so that the information can be retrieved using 
	 * getUserData.
	 * 
	 * @param key the key to use for retrieving the data
	 * @param data the data that has to be stored.
	 */
	public void storeData(Object key, Object data) {
		if (userData == null) {
			userData = new Hashtable();
		}
		userData.put(key, data);
	}

	/** 
	 * Retrieve data previously stored using storeData.
	 * 
	 * @param the key used to store the data.
	 */
	public Object getData(Object key) {
		if (userData == null) {
			return null;
		}
		return userData.get(key);
	}

	/**
	 * Remove the data stored with the specified key.
	 * 
	 * @param key the key corresponding to the information that should be 
	 * removed.
	 */
	public void removeData(Object key) {
		userData.remove(key);
		if (userData.isEmpty()) {
			// set userData to null so that it can be garbage collected
			userData = null;
		}
	}

	/** 
	 * Boolean indicating wether the file is external to the parsed package.
	 */
	protected boolean externalFile;

	public  JmlFile() {
	}

	public JmlFile(File file_name, AST a, JavaLoader p) {
		fileAST = a;
		fileName = new JmlEntryFile(file_name);
		classes = new Vector();
		importedPackages = new Vector();
		importedClasses = new Hashtable();
		filePackage = p.getRoot();
		externalFile = false;
	}

	public JmlFile(JmlFileEntry file_name, AST a, JavaLoader p, boolean external) {
		fileAST = a;
		fileName = file_name;
		classes = new Vector();
		importedPackages = new Vector();
		importedClasses = new Hashtable();
		filePackage = p.getRoot();
		externalFile = external;
	}

	public JmlFile(String fileName, Vector classes) {
		this.fileName = new JmlEntryFile(new File(fileName));
		this.classes = classes;
	}

	/**
	 * Returns the "flat name" for this <code>JmlFile</code>.
	 * <p>
	 * The flat name is a name that can be used as a B machine name,
	 * and reduce the probability of name conflicts between different classes 
	 * (such as classes with the same name in different packages).
	 * <p>
	 * It is currently equal to the name of the package this file belongs to,
	 * with dots replaced by underscores, and the name of the file without 
	 * its extension.
	 * 
	 * In case where the file belongs to the default package, the flat name
	 * correspond to the name of the file, without its extension.
	 */
	public String getFlatName(IPackage p) {
		// get the name of the file part
		String file_part = getFileName().getName();
		int ext_index = file_part.lastIndexOf('.');
		if (ext_index > 0) {
			file_part = file_part.substring(0, ext_index);
		}

		if (filePackage == null || filePackage == ((JavaLoader) p).getRoot()) {
			// if the file belongs to the default package
			return file_part;
		} else {
			return filePackage.getFullyQualifiedName().replace('.', '_')
				+ "_"
				+ file_part;
		}
	}

	/** 
	 * Return the filename corresponding to this file.
	 */
	public JmlFileEntry getFileName() {
		return fileName;
	}

	public String getFileNameAbsolutePath() {
		return fileName.getFile().getAbsolutePath();
	}

	/** 
	 * Return true if the file correspond to an external file.
	 */
	public boolean isExternal() {
		return externalFile;
	}

	/** 
	 * Return true if the given class_name correspond to an imported
	 * class.  
	 */
	public boolean isImportedClass(String class_name) {
		return importedClasses.containsKey(class_name);
	}

	/** 
	 * return the package corresponding to the given imported class.
	 * (i.e. a class imported as import package.class_name;)
	 * return null if the class is not imported 
	 */
	public Package getImportedClassPackage(String class_name) {
		return (Package) importedClasses.get(class_name);
	}

	/** 
	 * Parse the file
	 * <ul>
	 * <li> fills the package and import structures.
	 * <li> creates the class structures corresponding to the classes defined
	 * in this package
	 * </ul>
	 * @return the number of errors encountered.
	 */
	public int parse(IJml2bConfiguration config) {
		this.config = config;
		int error_count = 0;

		AST current = fileAST;
		while (current != null) {
			try {
				int node_type = current.getType();
				switch (node_type) {
					case JmlDeclParserTokenTypes.LITERAL_package :
						parsePackage(current, (JavaLoader) config.getPackage());
						break;
					case JmlDeclParserTokenTypes.LITERAL_import :
						parseImport(current, (JavaLoader) config.getPackage());
						break;
					case JmlDeclParserTokenTypes.MODIFIER_SET :
						parseClass(current);
						break;
				}
			} catch (ParseException e) {
				// print the error and continue
				// ErrorHandler.error(this, -1, -1, e.toString());
				++error_count;
			} catch (Jml2bException e) {
				ErrorHandler.error(this, -1, -1, e.toString());
				++error_count;
			}
			current = current.getNextSibling();
		}

		// add java.lang in the list of imported packages, if needed
		Package jl = ((JavaLoader) config.getPackage()).getJavaLang();
		if (!isImportedPackage(jl)) {
			importedPackages.add(jl);
		}

		if (!isExternal()) {
			// if the file does not belongs to an external package,
			// the package visible elements in classes loaded from
			// this package should be kept.
			filePackage.setKeepPackage(true);
		}

		return error_count;
	}

	protected boolean isImportedPackage(Package p) {
		Enumeration e = importedPackages.elements();
		while (e.hasMoreElements()) {
			Package current = (Package) e.nextElement();
			if (current == p) {
				return true;
			}
		}
		return false;
	}

	public void link(IJml2bConfiguration config) throws Jml2bException {
		LinkContext c = new LinkContext(this);
		// link each of the classes loaded
		Enumeration e = classes.elements();
		while (e.hasMoreElements()) {
			Class cl = (Class) e.nextElement();
			c.setCurrentClass(cl);
			cl.link(config, c);
		}
	}

	/**
	 * Links the statement parts of the file if needed.
	 */
	public int linkStatements(IJml2bConfiguration config)
		throws Jml2bException {
		//	if(isExternal()) {
		// not needed if the file is external
		//	    return;
		//	}
		LinkContext c = new LinkContext(this);
		// externally link each 
		Enumeration e = classes.elements();
		int errors = 0;
		while (e.hasMoreElements()) {
			Class cl = (Class) e.nextElement();
			c.setCurrentClass(cl);
			errors += cl.linkStatements(config, c);
		}
		return errors;
	}

	/**
	 * Links the statement parts of the file if needed.
	 */
	public void typeCheck(IJml2bConfiguration config) throws Jml2bException {
		LinkContext c = new LinkContext(this);
		Enumeration e = classes.elements();
		while (e.hasMoreElements()) {
			Class cl = (Class) e.nextElement();
			c.setCurrentClass(cl);
			cl.typeCheck(config, c);
		}
	}

	/*@ requires 
	  @   ast.getType() == JmlDeclParserTokenTypes.LITERAL_package;
	  @*/
	protected void parsePackage(AST ast, JavaLoader p) throws Jml2bException {
		filePackage = addPackages(config, ast.getFirstChild(), p.getRoot());
	}

	/*@ requires
	  @    ast.getType() == JmlDeclParserTokenTypes.LITERAL_import;
	  @*/
	protected void parseImport(AST ast, JavaLoader p) throws Jml2bException {
		// Il y a trois types de import:
		// 1) import a.b.C; 
		// 2) import a.b.*;
		// 3) import C;
		// 1 et 3 correspondent au cas ou l'on importe une classe.
		// 2 correspond au cas ou l'on importe l'ensemble des classes.
		ast = ast.getFirstChild();
		Package tmp_pkg = null;
		int token_type = ast.getType();

		if (token_type == JmlDeclParserTokenTypes.MODEL) {
			// case where we import a model. Skip the model tag
			ast = ast.getNextSibling();
		}

		switch (ast.getType()) {
			case JmlDeclParserTokenTypes.DOT :
				// on est soit dans le cas 1, soit dans le cas 2.
				// on ajoute les packages si n?cessaire, et on r?cupere une
				// r?ference sur le package correspondant
				ast = ast.getFirstChild();
				tmp_pkg = addPackages(config, ast, p.getRoot());

				ast = ast.getNextSibling();
				switch (ast.getType()) {
					case JmlDeclParserTokenTypes.IDENT :
						// case 1
						importClass(tmp_pkg, ast.getText());
						return;
					case JmlDeclParserTokenTypes.STAR :
						// case 2
						importedPackages.add(tmp_pkg);
						return;
					default :
						throw new ParseException(
							this,
							(LineAST) ast,
							"Unexpected token in parseImport");
				}
			case JmlDeclParserTokenTypes.IDENT :
				// case 3: importing class from current package
				importClass(filePackage, ast.getText());
				return;
			default :
				throw new ParseException(
					this,
					(LineAST) ast,
					"Unexpected token in parseImport");
		}
	}

	private void importClass(Package pkg, String class_name) {
		importedClasses.put(class_name, pkg);
	}

	/* @ requires
	  @    ast.getType() == JmlDeclParserTokenTypes.MODIFIER_SET;
	  @*/
	protected AST parseClass(AST ast) throws Jml2bException {
		Modifiers mods = new Modifiers(ast);
		ast = ast.getNextSibling();

		// in case we are parsing an external class, ignore classes that
		// are not externaly visible
		if (isExternal()
			&& !mods.isExternalVisible()
			&& !filePackage.keepPackageVisible()) {

			// do not ignore those classes, since they may be required
			// anyway

			//	    Debug.print("ignoring non-visible class");
			//	    return ast.getNextSibling();
		}

		Class cl = new Class(this, ast, filePackage, mods, externalFile);
		//        if(Debug.on) {
		//	        Debug.print(Debug.PARSING, "[Class: ");
		//        }
		AST res = cl.parse(this, ast);
		classes.add(cl);
		// add the class to loaded classes in the package
		filePackage.addClass(cl);
		//        if(Debug.on) {
		//	        Debug.print(Debug.PARSING, "]");
		//        }
		return res;
	}

	public Package getPackage() {
		return filePackage;
	}

	public Enumeration getClasses() {
		return classes.elements();
	}

	public Enumeration getImportedPackages() {
		return importedPackages.elements();
	}

	private static String jmlExtensions[] =
		{ ".refines-jml", ".jml", ".jml-refined", ".prop" };

	public static boolean isJmlFile(String s) {
		for (int i = 0; i < jmlExtensions.length; ++i) {
			if (s.length() > jmlExtensions[i].length()
				&& s.endsWith(jmlExtensions[i])) {
				return true;
			}
		}
		return false;
	}

	/** 
	 * parse a package AST clause, adding packages as needed. return
	 * the corresponding package 
	 */
	public static Package addPackages(IJml2bConfiguration config, AST ast, Package pkg) {
		String pkg_name;
		Package tmp_pkg;

		switch (ast.getType()) {
			case JmlDeclParserTokenTypes.IDENT :
				// add the package if it is needed.
				pkg_name = ast.getText();
				tmp_pkg = pkg.getPackage(pkg_name);

				if (tmp_pkg != null) {
					return tmp_pkg;
				} else {
					tmp_pkg = new Package(pkg_name);
					pkg.addPackage((JavaLoader) config.getPackage(), tmp_pkg);
					return tmp_pkg;
				}
			case JmlDeclParserTokenTypes.DOT :
				ast = ast.getFirstChild();
				tmp_pkg = addPackages(config, ast, pkg);
				ast = ast.getNextSibling();
				return addPackages(config, ast, tmp_pkg);
		}
		return null;
	}

	public static long getLoadedFilesCount() {
		return loadedFilesCount;
	}

	public static long getJmlParserTime() {
		return jmlParserTime;
	}

	public static void resetStats() {
		jmlParserTime = 0;
		loadedFilesCount = 0;
	}

	//	/**
	//	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	//	 **/
	//	public static Substitution loadSubstitution(
	//		IJml2bConfiguration config,
	//		JmlFile fi,
	//		JpoInputStream s)
	//		throws IOException, LoadException {
	//		switch (s.readByte()) {
	//			case Substitution.ARRAY_ELEMENT :
	//				{
	//					String st = s.readUTF();
	//					Formula f = Formula.create(config, s, fi);
	//					return new SubArrayElement(st, f);
	//				}
	//			case Substitution.ARRAY_LENGTH :
	//				{
	//					Formula f = Formula.create(config, s, fi);
	//					return new SubArrayLength(f);
	//				}
	//			case Substitution.FORM :
	//				{
	//					Formula f1 = Formula.create(config, s, fi);
	//					Formula f2 = Formula.create(config, s, fi);
	//					return new SubForm(f1, f2);
	//				}
	//			case Substitution.INSTANCES_SET :
	//				{
	//					Formula f = Formula.create(config, s, fi);
	//					return new SubInstancesSet(f);
	//				}
	//			case Substitution.INSTANCES_SINGLE :
	//				{
	//					Formula f = Formula.create(config, s, fi);
	//					return new SubInstancesSingle(f);
	//				}
	//			case Substitution.TMP_VAR :
	//				{
	//					String st = s.readUTF();
	//					Formula f = Formula.create(config, s, fi);
	//					return new SubTmpVar(st, f);
	//				}
	//			case Substitution.TYPEOF_SET :
	//				{
	//					Formula f = Formula.create(config, s, fi);
	//					Formula t = Formula.create(config, s, fi);
	//					return new SubTypeofSet(f, t);
	//				}
	//			case Substitution.TYPEOF_SINGLE :
	//				{
	//					Formula f = Formula.create(config, s, fi);
	//					Formula t = Formula.create(config, s, fi);
	//					return new SubTypeofSingle(f, t);
	//				}
	//			case Substitution.MEMBER_FIELD :
	//				{
	//					Formula f = Formula.create(config, s, fi);
	//					Formula b = Formula.create(config, s, fi);
	//					Formula c = Formula.create(config, s, fi);
	//					Formula d = Formula.create(config, s, fi);
	//					return new SubMemberField(f, b, c, d);
	//				}
	//			default :
	//				throw new LoadException("loadSubstitution : wrong type");
	//		}
	//
	//	}
	//
	//	/**
	//	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	//	 **/
	//	private static Method loadMethod(
	//		IJml2bConfiguration config,
	//		JmlFile fi,
	//		JpoInputStream s)
	//		throws IOException, LoadException {
	//		String name = s.readUTF();
	//		s.readBoolean(); // isConstructor
	//		s.readBoolean(); // isStatic
	//		s.readUTF(); // read the signature.
	//		String pmiName = s.readUTF();
	//		int firstLine = s.readInt();
	//		s.readInt(); // nbPO
	//		s.readInt(); // nbPoProved
	//		s.readInt(); // nbPoChecked
	//		return new Method(
	//			name,
	//			pmiName,
	//			new Proofs(config, fi, s),
	//			new Proofs(config, fi, s),
	//			firstLine);
	//	}

	//	/**
	//	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	//	 **/
	//	private static Class loadClass(
	//		IJml2bConfiguration config,
	//		JmlFile fi,
	//		JpoInputStream s)
	//		throws IOException, LoadException {
	//		String name = s.readUTF();
	//		int size = s.readInt();
	//		for (int i = 0; i < size; i++)
	//			s.readUTF();
	//		Proofs lemmas = new Proofs(config, fi, s);
	//		Proofs wellDefInvLemmas = new Proofs(config, fi, s);
	//		Vector constructors = new Vector();
	//		size = s.readInt();
	//		for (int j = 0; j < size; j++)
	//			constructors.add(loadMethod(config, fi, s));
	//		Vector methods = new Vector();
	//		size = s.readInt();
	//		for (int j = 0; j < size; j++)
	//			methods.add(loadMethod(config, fi, s));
	//		return new Class(name, lemmas, wellDefInvLemmas, constructors, methods);
	//
	//	}

	//	/**
	//	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	//	 **/
	//	public static JmlFile loadJmlFile(
	//		IJml2bConfiguration config,
	//		JpoInputStream s)
	//		throws IOException, LoadException {
	//		if (s.readInt() != JPO_FILE_FORMAT_VERSION)
	//			throw new LoadException("Wrong file format.");
	//		JmlFile jmlFile = new JmlFile();
	//		String filename = s.readUTF();
	//		s.readInt(); // Po 
	//		s.readInt(); // PoProved
	//		int nbLang = s.readInt(); // neLanguages
	//		if (nbLang != Languages.getNbLanguages())
	//			throw new LoadException("Wrong file format");
	//		jmlFile.langNames = new String[nbLang];
	//		for (int i = 0; i < nbLang; i++) {
	//			jmlFile.langNames[i] = s.readUTF();
	//			if (Languages.getIndex(jmlFile.langNames[i]) != i)
	//				throw new LoadException("Wrong file format");
	//			s.readInt(); // nbPoProved
	//		}
	//		int size = s.readInt();
	//		jmlFile.depends = new Vector();
	//		for (int j = 0; j < size; j++)
	//			jmlFile.depends.add(s.readUTF());
	//		Vector classes = new Vector();
	//		size = s.readInt();
	//		for (int j = 0; j < size; j++)
	//			classes.add(loadClass(config, jmlFile, s));
	//		jmlFile.fileName = new File(filename);
	//		jmlFile.classes = classes;
	//
	//		return jmlFile;
	//	}

	//	/**
	//	 * Package this files belongs to. It is set to root if the package is 
	//	 * unnamed.
	//	 */
	//	private static boolean equals(Package fp1, Package fp2) {
	//		return (
	//			(fp1 == null && fp2 == null)
	//				|| (fp1.name.equals(fp2.name) && equals(fp1.parent, fp2.parent)));
	//	}

	// number of milliseconds spent in the JML parser
	public static long jmlParserTime = 0;
	public static long loadedFilesCount = 0;

	/**
	 * @return Vector
	 */
	public Vector getDepends() {
		return depends;
	}

	/**
	 * Sets the depends.
	 * @param depends The depends to set
	 */
	public void setDepends(Vector depends) {
		this.depends = depends;
	}

	static final long serialVersionUID = -4142771309661361450L;

//	/**
//	 * @param file
//	 */
//	public void setFileName(File file) {
//		fileName = file;
//	}


	/**
	 * 
	 */
	public String[] getLangNames() {
		return langNames;

	}

	/**
	 * @return
	 */
	public IJml2bConfiguration getConfig() {
		return config;
	}

	/**
	 * @return
	 */
	public AST getFileAST() {
		return fileAST;
	}

	/**
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 **/
	public static final int JPO_FILE_FORMAT_VERSION = 29;
	
	
}