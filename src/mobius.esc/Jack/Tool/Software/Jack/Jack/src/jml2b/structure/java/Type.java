//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Type.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.java;

import java.io.Serializable;
import java.util.Enumeration;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.ParseException;
import jml2b.exceptions.TokenException;
import jml2b.languages.ITranslationResult;
import jml2b.languages.Languages;
import jml2b.link.LinkContext;
import jml2b.link.Linkable;
import jml2b.structure.statement.MyToken;
import jml2b.util.Util;
import antlr.collections.AST;

/**
 * Class representing types. Types can correspond to builtin types
 * (<code>int</code>, <code>short</code>, etc...), reference types
 * (correspoding to references to classes) or array types.
 * 
 * Types contains a tag that describes the type information available.
 * The tag can be equal to:
 * <ul>
 * <li><code>T_VOID</code>, only used for describing return values. 
 *     Correspond to the <code>void</code> return value. 
 * <li><code>T_BOOLEAN</code>, indicating that the type corresponds to the 
 * 	   <code>boolean</code> builtin type.
 * <li><code>T_BYTE</code>, indicating that the type corresponds to the
 *     <code>byte</code> builtin type.
 * <li><code>T_SHORT</code>, indicating that the type corresponds to the
 *     <code>short</code> builtin type.
 * <li><code>T_CHAR</code>, indicating that the type corresponds to the 
 *     <code>char</code> builtin type.
 * <li><code>T_DOUBLE</code>, indicating that the type corresponds to the 
 * 	   <code>double</code> builtin type.
 * <li><code>T_FLOAT</code>, indicating that the type corresponds to the 
 *     <code>float</code> builtin type.
 * <li><code>T_INT</code>, indicating that the type corresponds to the 
 *     <code>int</code> builtin type.
 * <li><code>T_LONG</code>, indicating that the type corresponds to the
 *     <code>long</code> builtin type.
 * <li><code>T_NULL</code>, indicating that the type corresponds to a
 *     <code>null</code> reference. Such type should never occur in a
 *     signature, and is only used internally.
 * <li><code>T_TYPE</code>, indicating that the type corresponds to a
 *     type. The jml <code>\type</code> operator can produce such 
 *     types.
 * <li><code>T_REF</code>, indicating that the type corresponds to a 
 *     reference to a class. The corresponding class can be accessed using
 *     the <code>getRefType</code> method.
 * <li><code>T_ARRAY</code>, indicating that the type corresponds to a
 *     reference to an array. The type describing the elements stored 
 *     within the array is obtained using the <code>getElemType</code>
 *     method. For those types, the <code>getRefType</code> method can be
 *     called and will return the special "array" class.
 * </ul>
 * 
 * @author A. Requet L. Burdy
 * 
 * @see Type#getRefType();
 * @see Type#getElemType();
 */
public class Type
	extends ParsedItem
	implements Linkable, JmlDeclParserTokenTypes, Serializable, IType {

	public static Type binaryNumericPromotion(Type t1, Type t2) {
		if (t1.tag == T_DOUBLE)
			return t1;
		if (t2.tag == T_DOUBLE)
			return t2;
		if (t1.tag == T_FLOAT)
			return t1;
		if (t2.tag == T_FLOAT)
			return t2;
		if (t1.tag == T_LONG)
			return t1;
		if (t2.tag == T_LONG)
			return t2;
		else
			return $int;
	}

	/**
	 * Tag describing the type of the Type (int, ref, refarray, etc...)
	 **/
	protected /*@ spec_public */
	int tag;

	/**
	 * AST representing the type in case of a reference type.
	 */
	protected transient AST classAST;

	/**
	 * Class of a reference type.
	 */
	protected /*@ spec_public */
	AClass refType;
	
	public void setRefType (AClass clazz){
		if(tag == T_REF)
			refType = clazz;
	}
	
	/**
	 * Type of elements stored in a reference array.
	 */
	protected /*@ spec_public */
	Type elemType;


	public Type() {
		super();
	}

	public Type(IJml2bConfiguration config, String typeDescriptor) {
		switch (typeDescriptor.charAt(0)) {
			case 'B' :
				tag = T_BYTE;
				break;
			case 'C' :
				tag = T_CHAR;
				break;
			case 'I' :
				tag = T_INT;
				break;
			case 'S' :
				tag = T_SHORT;
				break;
			case 'Z' :
				tag = T_BOOLEAN;
				break;
			case 'V' :
				tag = T_VOID;
				break;
			case 'L' :
				tag = T_REF;
				refType =
					((JavaLoader) config.getPackage()).getRoot().searchClass(
						typeDescriptor.substring(
							1,
							typeDescriptor.indexOf(';')));
				break;
			case '[' :
				tag = T_ARRAY;
				elemType = new Type(config, typeDescriptor.substring(1));
				break;
			default :
				tag = T_REF;
				refType = ((JavaLoader) config.getPackage()).getRoot().searchClass(typeDescriptor);
				break;

		}

	}

	/**
	 * Creates a new builtin type with the given tag.
	 * The tag should correspond to a builtin type and should not be equal 
	 * to <code>T_REF</code> or <code>T_ARRAY</code>, since those tags 
	 * requires additional information (reference type and array type).
	 * 
	 * @param tag the builtin type.
	 */
	/*@ requires tag != T_REF && tag != T_ARRAY;
	  @*/
	public Type(int tag) {
		super();
		this.tag = tag;
		refType = null;
	}

	/**
	 * Creates a new type corresponding to the given class.
	 * The resulting type will have tag <code>T_REF</code>, and its
	 * reference type will be set to <code>cl</code>.
	 * 
	 * @param cl the class described by the resultin type. Should not be 
	 *     <code>null</code>.
	 */
	/*@ requires cl != null;
	  @ ensures  tag == T_REF && refType == cl;
	  @*/
	public Type(AClass cl) {
		super();
		if (cl == null) {

			throw new InternalError("Trying to create class type with null");
		}
		this.tag = T_REF;
		refType = cl;
	}

	/**
	 * Creates a new array class containing the given elements.
	 * 
	 * @param config the configuration to use for loading new classes. It
	 *     is required, since calling this constructor may theorically trigger
	 *     the loading of the <code>java.lang.Object</code> class.
	 * @param t the type of the elements stored within the array. This
	 *     parameter should not be <code>null</code>.
	 */
	/*@ requires t != null;
	  @ ensures  tag == T_ARRAY && elemType == t;
	  @*/
	public Type(IJml2bConfiguration config, Type t) throws Jml2bException {
		super();
		this.tag = T_ARRAY;
		elemType = t;
		// set reftype so that it points to the array class
		refType = config.getArray();
	}

	/**
	 * Creates a new array type using the given type as elements.
	 * This constructor does not requires a configuration, since it
	 * aims to be called during parsing, and does not initialize the
	 * element type.
	 * <p>
	 * The element type will be initialised later, during the linking 
	 * phase. 
	 * This constructor is called from the <code>addDims</code> method.
	 * 
	 * @param t The type of the elements. Should not be <code>null</code>.
	 * @see addDims(JmlFile, AST, Type);
	 */
	/*@ requires t != null;
	  @ ensures  tag == T_ARRAY && elemType == t;
	  @*/
	public Type(Type t) {
		super();
		this.tag = T_ARRAY;
		elemType = t;
		// set reftype so that it points to the array class
		// refType = Class.getArray(config);
	}

	/**
	 * Creates a new type from the given AST.
	 * 
	 * @param jf the file where the type occured.
	 * @param tree the AST corresponding to the type.
	 */
	public Type(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Creates a new unlinked type with the given AST. 
	 * Constructor used by the <code>createUnlinkedClass(String)</code> 
	 * method.
	 * 
	 * @param tree the AST corresponding to the type.
	 * @see Type#createUnlinkedClass(String);
	 */
	private Type(AST tree) {
		super();
		tag = T_REF;
		classAST = tree;
	}

	/**
	 *  create a type from the given AST. The AST must point to a type
	 *  declaration.
	 **/
	/*@
	  @ requires type_ast != null;
	  @ ensures \result != null;
	  @*/
	public AST parse(AST type_ast) throws Jml2bException {
		// create a new temporary type
		Type tmp = new Type(getJmlFile(), type_ast);
		// parse it as a primitive type (i.e. not array)
		tmp.parsePrimitive(type_ast);
		type_ast = type_ast.getNextSibling();

		if (type_ast != null && type_ast.getType() == DIMS) {
			tmp = addDims(getJmlFile(), type_ast, tmp);
			type_ast = type_ast.getNextSibling();
		}

		set(tmp);
		return type_ast;
	}

	public boolean equals(Type t) {
		return tag == t.getTag()
			&& (tag != T_REF || refType.equals(t.refType))
			&& (tag != T_ARRAY || elemType.equals(t.elemType));
	}

	/**
	 * copy t into this.
	 * 
	 * @param t the type to copy.
	 **/
	private void set(Type t) {
		tag = t.tag;
		classAST = t.classAST;
		refType = t.refType;
		elemType = t.elemType;
		setBox(t);
	}

	/* @ requires type_ast.getType() == IDENT ||
	  @          type_ast.getType() == DOT ||
	  @		 type_ast.getType() == JAVA_BUILTIN_TYPE;
	  @*/
	private void parsePrimitive(AST type_ast) throws ParseException {
		switch (type_ast.getType()) {
			case IDENT :
				//				setY(type_ast.getText().length());
			case DOT :
				tag = T_REF;
				refType = null;
				elemType = null;
				classAST = type_ast;
				break;
			case JAVA_BUILTIN_TYPE :
				if (!setBuiltin(type_ast.getText())) {
					throw new ParseException(
						getJmlFile(),
						(LineAST) type_ast,
						"Unknown builtin type : " + type_ast.getText());
				}
				//				setY(type_ast.getText().length());
				break;
			case T_TYPEOFALLTYPES :
				tag = T_TYPE;
				break;
			default :
				throw new TokenException(
					getJmlFile(),
					(LineAST) type_ast,
					"Type.parsePrimitive (ast text: "
						+ type_ast.getText()
						+ ", line = "
						+ ((jml.LineAST) (type_ast)).line
						+ ")",
					"IDENT, DOT or JAVA_BUILTIN_TYPE ",
					type_ast.getType()
						+ " ("
						+ MyToken.nodeString[type_ast.getType()]
						+ ")");
		}
	}

	/*@ ensures tag == T_REF ==> refType != null; 
	  @*/
	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (isBuiltin()) {
			// nothing to do.
			return;
		} else if (isArray()) {
			// link the element type.
			elemType.link(config, f);
			refType = config.getArray();
		} else {
			// in case the type is already linked (should not happen)
			if (refType != null) {
				return;
			}

			// we know that classAST is either DOT, either IDENT
			switch (classAST.getType()) {
				case DOT :
					// this is an fully qualified name class
					linkFullRef(config, f);
					break;
				case IDENT :
					// this is a short name class
					linkShortRef(config, classAST.getText(), f);
					break;
				default :
					throw new TokenException(
						getJmlFile(),
						(LineAST) classAST,
						"Type.link",
						"DOT or IDENT",
						classAST.getType());
			}

			// "free" the classAST
			classAST = null;
		}
	}
	// @ requires refType != null;
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return 0;
		/*
		  if(tag == T_REF) {
		  getRefType().linkStatements(f);
		  } else if(tag == T_ARRAY) {
		  getElemType().linkStatements(f);
		  }
		*/
	}

	private void linkFullRef(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		AST package_ast = classAST.getFirstChild();
		AST class_ast = package_ast.getNextSibling();

		if (class_ast.getType() != IDENT) {
			throw new LinkException("Unexpected token in linkFullRef", this);
		}

		String class_name = class_ast.getText();
		Package p = JmlFile.addPackages(config, package_ast, ((JavaLoader) config.getPackage()).getRoot());

		refType = p.getAndLoadClass(config, class_name);

		// ensure that the class is correctly linked
		if (refType == null) {
			throw new LinkException(
				"linkFullRef : Could not link class : " + class_name,
				this);
		}
	}

	private void linkShortRef(
		IJml2bConfiguration config,
		String class_name,
		LinkContext f)
		throws Jml2bException {
		AClass result;
		// in this case, class_name is either:
		// - a class in the current package
		// - a class imported as package.Class;
		// - a class in the list of packages imported as package.* or in 
		//   java.lang

		// search in the current package. The class *must* already be loaded
		Package p = f.getPackage();
		result = p.getAndLoadClass(config, class_name);

		if (result == null) {
			// the class is not in the current package, look in classes
			// imported as import package.Class;
			p = f.getImportedClassPackage(class_name);

			if (p != null) {
				// in this case, we know that the class belongs to this 
				// package. 
				result = p.getAndLoadClass(config, class_name);
			} else {
				// the class is one of the classes located in the import
				// clauses
				// search each of the imported package for loading
				Enumeration e = f.getImportedPackages();
				while (e.hasMoreElements()) {
					p = (Package) e.nextElement();
					result = p.getAndLoadClass(config, class_name);
					if (result != null) {
						break;
					}
				}
			}
		}
		if (result == null) {
			throw new LinkException(
				"linkShortRef: Could not link class : " + class_name,
				this);
		}
		refType = result;
	}

	/**
	 * Returns the reference type for references or array types.
	 *  
	 * @return Class the class of the reference type.
	 */
	/*@ requires tag == T_REF || tag == T_ARRAY;
	  @ ensures  \result != null && \result == refType;
	  @*/
	public AClass getRefType() {
		return refType;
	}

	/**
	 * Returns the type of the elements of an array type.
	 * The current type should be an array type. That is it should
	 * have the tag <code>T_ARRAY</code>.
	 *  
	 * @return Type the type of the elements that are stored within 
	 *     the array. 
	 */
	/*@ requires tag == T_ARRAY;
	  @ ensures \result != null && \result == elemType;
	  @*/
	public Type getElemType() {
		return elemType;
	}

	/** 
	 * Set the current type to represent a builtin type of the type 
	 * <code>type_tag</code>.
	 * 
	 * @param type_tag the type to which the type should be set. It should
	 *     correspond to a primitive type.
	 */
	public void setBuiltin(int type_tag) {
		tag = type_tag;
		refType = null;
		elemType = null;
	}

	/** 
	 * Set the current type to represent a builtin type of the typ described by 
	 * the given string.
	 * 
	 * @param type_name the name of the type.
	 * @return true on success, false if the string was not understood.  
	 */
	public boolean setBuiltin(String type_name) {
		if (type_name.equals("int")) {
			setBuiltin(T_INT);
		} else if (type_name.equals("short")) {
			setBuiltin(T_SHORT);
		} else if (type_name.equals("char")) {
			setBuiltin(T_CHAR);
		} else if (type_name.equals("byte")) {
			setBuiltin(T_BYTE);
		} else if (type_name.equals("boolean")) {
			setBuiltin(T_BOOLEAN);
		} else if (type_name.equals("void")) {
			setBuiltin(T_VOID);
		} else if (type_name.equals("double")) {
			setBuiltin(T_DOUBLE);
		} else if (type_name.equals("float")) {
			setBuiltin(T_FLOAT);
		} else if (type_name.equals("long")) {
			setBuiltin(T_LONG);
		} else {
			return false;
		}
		return true;
	}

	public boolean equals(Object o) {
		if (o instanceof Type) {
			Type t = (Type) o;
			if (tag == t.tag) {
				if (isBuiltin()) {
					// in the case where two builtin types have same tag,
					// they are be equal
					return true;
				}
				if (isArray()) {
					// two refarray types are equals iff the type of their
					// elements are equals
					return getElemType().equals(t.getElemType());
				}

				// in this case, we know that the tag is T_REF.
				// So, the two types are equals iff their classes are.
				// return getRefType().equals(t.getRefType());
				return getRefType() == t.getRefType();
			} else {
				// two types can't be equals if they have different tags
				return false;
			}
		}
		return false;
	}

	/** 
	 * Returns true if this type correspond to an array type.
	 * 
	 * @return <code>true</code> if the type is an array type, 
	 *     <code>false</code> otherwise.
	 */
	public boolean isArray() {
		return tag == T_ARRAY;
	}

	/** 
	 * Returns true if the type is a builtin-type. Note that the type 
	 * <code>T_TYPE</code> is considered a builtin-type.
	 * 
	 * @return <code>true</code> if the type is a builtin one, 
	 *    <code>false</code> otherwise. 
	 */
	public boolean isBuiltin() {
		switch (tag) {
			case T_INT :
			case T_SHORT :
			case T_CHAR :
			case T_BYTE :
			case T_BOOLEAN :
			case T_VOID :
			case T_LONG :
			case T_FLOAT :
			case T_DOUBLE :
			case T_TYPE :
				return true;

			case T_NULL :
			case T_ARRAY :
			case T_REF :
			case T_CLASS :
				return false;
		}
		throw new InternalError("Unhandled case in Type.isBuiltin() : " + tag);
	}

	public boolean isIntegral() {
		switch (tag) {
			case T_INT :
			case T_SHORT :
			case T_CHAR :
			case T_BYTE :
			case T_LONG :
				return true;

			case T_FLOAT :
			case T_DOUBLE :
			case T_TYPE :
			case T_BOOLEAN :
			case T_VOID :
			case T_NULL :
			case T_ARRAY :
			case T_REF :
			case T_CLASS :
				return false;
		}
		throw new InternalError("Unhandled case in Type.isBuiltin() : " + tag);
	}

	public boolean isNumeric() {
		switch (tag) {
			case T_INT :
			case T_SHORT :
			case T_CHAR :
			case T_BYTE :
			case T_LONG :
			case T_FLOAT :
			case T_DOUBLE :
				return true;

			case T_TYPE :
			case T_BOOLEAN :
			case T_VOID :
			case T_NULL :
			case T_ARRAY :
			case T_REF :
			case T_CLASS :
				return false;
		}
		throw new InternalError("Unhandled case in Type.isBuiltin() : " + tag);
	}

	public boolean isRef() {
		switch (tag) {
			case T_NULL :
			case T_ARRAY :
			case T_REF :
				return true;

			case T_INT :
			case T_SHORT :
			case T_CHAR :
			case T_BYTE :
			case T_LONG :
			case T_FLOAT :
			case T_DOUBLE :
			case T_TYPE :
			case T_BOOLEAN :
			case T_VOID :
			case T_CLASS :
				return false;
		}
		throw new InternalError("Unhandled case in Type.isBuiltin() : " + tag);
	}

	public Type unaryPromote() {
		switch (tag) {
			case T_INT :
			case T_SHORT :
			case T_CHAR :
			case T_BYTE :
				return $int;
			case T_DOUBLE :
			case T_FLOAT :
			case T_LONG :
				return this;
		}
		throw new InternalError(
			"Unhandled case in Type.unaryPromote() : " + tag);
	}

	public boolean isBoolean() {
		return tag == T_BOOLEAN;
	}

	/** 
	 * return the dimension of the type. If the type is not an array, then its 
	 * dimension is equal to 0. Otherwise, it is equal to the dimension of the 
	 * array. 
	 * 
	 * @return the dimension of the type.
	 */
	public int getDimension() {
		switch (tag) {
			case T_INT :
			case T_CHAR :
			case T_BYTE :
			case T_SHORT :
			case T_BOOLEAN :
			case T_REF :
			case T_VOID :
			case T_FLOAT :
			case T_DOUBLE :
			case T_LONG :
			case T_TYPE :
			case T_CLASS :
				return 0;
			case T_ARRAY :
				return getElemType().getDimension() + 1;
		}
		// should not reach this point
		throw new InternalError(
			"Unhandled case in Type.getDimension() : " + tag);
	}

	/**
	 * Returns the class that is the type of the object or of the element of the
	 * type if it is an array.
	 **/
	public AClass getTargetedClass() {
		switch (tag) {
			case T_REF :
				return refType;
			case T_ARRAY :
				return getElemType().getTargetedClass();
			default :
				return null;
		}

	}

	/**
	 * Returns the tag describing the type of the type.
	 * 
	 * @return int the tag corresponding to the type.
	 */
	/*@ ensures \result == tag;
	  @*/
	public int getTag() {
		return tag;
	}

	private static AST createAST(int type, String content) {
		AST result = new antlr.CommonAST();
		result.setType(type);
		result.setText(content);
		return result;
	}

	/**
	 * Creates an unlinked type element corresponding to the given fully
	 * qualified class name.
	 * 
	 * @param fqn the fully qualified name of the class.
	 * @return a type describing the given class, that should be linked.
	 */
	public static Type createUnlinkedClass(String fqn) {
		String[] idents = Util.tokenize(fqn, ".");
		// error
		if (idents.length < 1) {
			return null;
		}

		AST res = createAST(IDENT, idents[0]);

		for (int i = 1; i < idents.length; ++i) {
			AST dot = createAST(DOT, null);
			res.setNextSibling(createAST(IDENT, idents[i]));
			dot.setFirstChild(res);
			res = dot;
		}

		return new Type(res);
	}

	/**
	 * Converts the type to a java representation.
	 * 
	 * @return String a string corresponding to the type using a 
	 *     Java-like notation.
	 */
	public String toJava() {
		switch (tag) {
			case T_INT :
				return "int";
			case T_SHORT :
				return "short";
			case T_BYTE :
				return "byte";
			case T_BOOLEAN :
				return "boolean";
			case T_CHAR :
				return "char";
			case T_VOID :
				return "void";
			case T_LONG :
				return "long";
			case T_DOUBLE :
				return "double";
			case T_FLOAT :
				return "float";
			case T_TYPE :
				return "\\TYPE";
			case T_CLASS :
				return "class";
			case T_NULL :
				return "null";
			case T_REF :
				if (refType != null) {
					return refType.getName();
				} else {
					return "T_REF null";
				}
			case T_ARRAY :
				if (elemType != null) {
					return elemType.toJava() + "[]";
				} else {
					return "[] null";
				}
			default :
				throw new InternalError("Type.ToJava() unknown tag : " + tag);
		}
	}

	/**
	 * return a code used to compare builtin types (it is an integer increasing 
	 * with the range of the type) 
	 * (byte < short < int < long < float < double).
	 * 
	 * Note that the definition of a builtin type is different from the one
	 * used in the <code>isBuiltin</code> method.
	 * 
	 * Here, a builtin type corresponds to one of the following:
	 * <ul>
	 * <li><code>byte</code>
	 * <li><code>short</code>
	 * <li><code>char</code>
	 * <li><code>int</code>
	 * <li><code>long</code>
	 * <li><code>float</code>
	 * <li><code>double</code>
	 * </ul>
	 * 
	 * @return int the comparison code.
	 */
	private int getBuiltinCode() {
		switch (tag) {
			case T_BYTE :
				return 1;
			case T_SHORT :
				return 2;
			case T_CHAR :
				return 2;
			case T_INT :
				return 3;
			case T_LONG :
				return 4;
			case T_FLOAT :
				return 5;
			case T_DOUBLE :
				return 6;
			default :
				return -1;
		}
	}

	/**
	 * compare two different builtin types.
	 */
	/* @ requires isBuiltin() == true && t.isBuiltin() == true;
	  @ requires tag != t.tag;
	  @*/
	private boolean isBuiltinSubtypeOf(Type t) {
		if (tag == T_BOOLEAN || tag == T_TYPE) {
			return false;
		}
		if (t.tag == T_CHAR) {
			// "this" is different from char, and char has no subtype =>
			// "this" cannot be a subtype of char
			return false;
		}

		return getBuiltinCode() < t.getBuiltinCode();
	}

	/**
	 * return true iff this is a subtype of the given type. That is if 
	 * <code>this</code> can be converted implicitely to <code>t</code>.
	 * 
	 * This method will return <code>true</code> in the case where the
	 * types are equals. 
	 * 
	 * @param config the configuration that should be used for loading
	 *     new classes.
	 * @param t the type that should be compared.
	 * @return <code>true</code> if the current type is a subtype of 
	 *     <code>t</code>, <code>false</code> otherwise.
	 **/
	public boolean isSubtypeOf(IJml2bConfiguration config, Type t) {
		if (tag == T_VOID || t.tag == T_VOID) {
			throw new InternalError(
				"Should never compare void types in " + "valid java classes");
			//return false;
		}
		// if the types are equals, then return true
		if (equals(t)) {
			return true;
		}

		// two different builtin types cannot be equals
		if (isBuiltin()) {
			if (t.isBuiltin()) {
				return isBuiltinSubtypeOf(t);
			} else {
				// a builtin type cannot be a subtype of a reference or array
				// type.
				return false;
			}
		}
		if (t.isBuiltin()) {
			// if we are not a builtin type and t is a builtin type, it is 
			// not possible to be a subtype of t
			return false;
		}

		// at this point, we know that neither this nor t are builtin types.

		if (tag == T_NULL) {
			// null is a subtype of any reference type
			return true;
		}

		if (t.tag == T_NULL) {
			return false;
		}

		if (isArray()) {
			if (t.isArray()) {
				// if the other type is an array, then 
				return getElemType().isSubtypeOf(config, t.getElemType());
			} else {
				try {
					return config.getObject().isSubtypeOf(config, t);
				} catch (Jml2bException je) {
					throw new InternalError(je.getMessage());
				}
			}
		}
		// a reference type cannot be a subtype of an array type
		if (t.isArray()) {
			return false;
		}
		// class of t
		AClass t_class = t.getRefType();
		// class of this
		AClass cl = getRefType();

		if (t_class.isInterface()) {
			// in that case, search the implements list for t_class
			return cl.implementsInterface(t_class);
		} else {
			// search superClass until we reach Object or t_class
			while (cl != t_class) {
				if (cl.isObject()) {
					return false;
				}
				cl = cl.getSuper().getRefType();
			}

			return true;
		}
	}


//	/**
//	 * Sets typeObject to null. This method is called by 
//	 * Package.clearAll();
//	 */
//	public static void clearAll() {
//		typeObject = null;
//	}

	/**
	 * count the number of dimensions in the given ast.
	 */
	// @ requires dims_ast.getType() == JmlDeclParserTokenTypes.DIMS;
	public static Type addDims(JmlFile jmlFile, AST dims_ast, Type t)
		throws Jml2bException {
		AST tmp = dims_ast.getFirstChild();
		Type res = t;

		while (tmp != null) {
			if (tmp.getType() == LBRACK) {
				res = new Type(res);
			} else {
				throw new ParseException(
					jmlFile,
					(LineAST) dims_ast,
					"VarDeclParser: Unexpected token counting dims");
			}
			tmp = tmp.getNextSibling();
		}
		return res;
	}

	/**
	 * Converts a signature to a string suitable for printing.
	 * The given enumeration should enumerate <code>Type</code>
	 * elements.
	 * 
	 * @param e the enumeration corresponding to the signature.
	 * @return String a <code>String</code> representation of the
	 *     signature. 
	 */
	public static String signatureToString(Enumeration e) {
		String result = "";
		boolean is_first = true;

		while (e.hasMoreElements()) {
			if (is_first) {
				is_first = false;
			} else {
				result += ", ";
			}
			Type t = (Type) e.nextElement();
			result += t.toJava();
		}
		return result;
	}

	/**
	 * Returns a type corresponding to the <code>boolean</code> builtin 
	 * type.
	 * This method is prefered to using <code>new Type(T_BOOLEAN)</code>,
	 * since it reuses the same instance for each type, thus reducing
	 * memory use. 
	 * 
	 * @return Type a type describing the <code>boolean</code> builtin
	 *     type.
	 */
	public static Type getBoolean() {
		return $boolean;
	}

	/**
	 * Returns a type corresponding to the <code>int</code> builtin 
	 * type.
	 * This method is prefered to using <code>new Type(T_INT)</code>,
	 * since it reuses the same instance for each type, thus reducing
	 * memory use. 
	 * 
	 * @return Type a type describing the <code>int</code> builtin
	 *     type.
	 */
	public static Type getInteger() {
		return $int;
	}

	/**
	 * Returns a type corresponding to the <code>char</code> builtin 
	 * type.
	 * This method is prefered to using <code>new Type(T_CHAR)</code>,
	 * since it reuses the same instance for each type, thus reducing
	 * memory use. 
	 * 
	 * @return Type a type describing the <code>char</code> builtin
	 *     type.
	 */
	public static Type getChar() {
		return $char;
	}

	public static Type getByte() {
		return $byte;
	}

	public static Type getShort() {
		return $short;
	}

	/**
	 * Returns a type corresponding to the <code>type</code> builtin 
	 * type.
	 * This method is prefered to using <code>new Type(T_TYPE)</code>,
	 * since it reuses the same instance for each type, thus reducing
	 * memory use. 
	 * 
	 * @return Type a type describing the <code>type</code> builtin
	 *     type.
	 */
	public static Type getType() {
		return $type;
	}

	public String toString() {
		return toJava();
	}

	public ITranslationResult toLang(String language)
		throws LanguageException {
		return Languages.getLanguageClass(language).typeFactory(this).toLang(0);
	}

	public void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	// constants for the different types.
	/**
	 * Constant representing the <code>int</code> type.
	 */
	public static final int T_INT = 1;
	/**
	 * Constant representing the <code>short</code> type.
	 */
	public static final int T_SHORT = 2;
	/**
	 * Constant representing the <code>byte</code> type.
	 */
	public static final int T_BYTE = 3;
	/**
	 * Constant representing the <code>boolean</code> type.
	 */
	public static final int T_BOOLEAN = 4;
	/**
	 * Constant representing the <code>char</code> type.
	 */
	public static final int T_CHAR = 5;
	/**
	 * Constant used to tag references to classes. For types that have this
	 * tag, information on the referenced class can be obtained using the 
	 * <code>getRefType()</code> method.
	 * 
	 * @see Type#getRefType();
	 */
	public static final int T_REF = 6;

	/**
	 * indicate an array type. For types that have this tag, information on
	 * the element type can be obtained using the <code>getElemType()</code>
	 * method.
	 * 
	 * Additionally, the <code>getRefType()</code> method can be called and
	 * will return the special "array" class.
	 * 
	 * @see Type#getElemType();
	 * @see Type#getRefType();
	 */
	public static final int T_ARRAY = 7;

	/**
	 * Constant representing the <code>void</code> type.
	 */
	public static final int T_VOID = 8;
	/**
	 * Constant representing the <code>float</code> type.
	 */
	public static final int T_FLOAT = 9;
	/**
	 * Constant representing the <code>long</code> type.
	 */
	public static final int T_LONG = 10;
	/**
	 * Constant representing the <code>double</code> type.
	 */
	public static final int T_DOUBLE = 11;
	/**
	 * Constant representing the <code>null</code> type. Although this
	 * type will not appear directly in the source code (i.e. it is not
	 * possible to declare variables having this type), it is required 
	 * internally for the method lookup and type checking.
	 */
	public static final int T_NULL = 12;

	/**
	 * used for return values of \elemtype and \type
	 */
	public static final int T_TYPE = 13;

	/**
	 * used for typing class expression: this should always result in a typecheck error
	 */
	public static final int T_CLASS = 14;

	/**
	 * Instance of the <code>boolean</code> type returned by the 
	 * <code>getBoolean()</code> method.
	 */
	private static final Type $boolean = new Type(T_BOOLEAN);
	/**
	 * Instance of the <code>int</code> type returned by the 
	 * <code>getInteger()</code> method.
	 */
	public static final Type $int = new Type(T_INT);
	/**
	 * Instance of the <code>char</code> type returned by the 
	 * <code>getChar()</code> method.
	 */
	public static final Type $char = new Type(T_CHAR);

	public static final Type $byte = new Type(T_BYTE);
	public static final Type $short = new Type(T_SHORT);

	/**
	 * Instance of the <code>type</code> type returned by the 
	 * <code>getType()</code> method.
	 */
	public static final Type $type = new Type(T_TYPE);


	static final long serialVersionUID = -3537023320146708719L;


}