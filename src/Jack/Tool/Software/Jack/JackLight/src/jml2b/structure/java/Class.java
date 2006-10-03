//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Class.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.java;

import jack.util.Logger;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.ParseException;
import jml2b.exceptions.TokenException;
import jml2b.link.LinkContext;
import jml2b.link.LinkUtils;
import jml2b.link.Linkable;
import jml2b.link.TypeCheckable;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.structure.IAParameters;
import jml2b.structure.jml.Depends;
import jml2b.structure.jml.JmlExpression;
import jml2b.structure.jml.Represents;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.StSkip;
import jml2b.structure.statement.TerminalExp;
import antlr.collections.AST;

/**
 * Internal representation of classes.
 * 
 * @author A. Requet, L. Burdy.
 */
public class Class
extends AClass
	implements Linkable, Serializable, TypeCheckable {
	/** 
	 * The link state the class is in. 
	 */
	protected int linkedState;

	/** 
	 * The package the class belongs to. 
	 */
	private Package classPackage;

	/** 
	 * The modifiers of the class (i.e. public, protected, etc...). 
	 */
	private Modifiers modifiers = new Modifiers(0);

	/** 
	 * (short) name of the class. 
	 */
	private String name;

	/** 
	 * True if the class is an interface, false otherwise. 
	 */
	boolean interfaceModifier;

	/** 
	 * Identifiers of implemented interfaces. Vector of <code>Type</code>
	 * elements.
	 * 
	 * @see Type
	 */
	Vector implementedInterfaces;

	/** 
	 * Fields defined by the class. (Vector of <code>JmlFields</code>). 
	 * Note that Those fields do not include fields defined by the 
	 * superclass.
	 * 
	 * @see Field
	 */
	public Vector fields;

	/** 
	 * Member invariants defined by the class. (Vector of jml2b.Invariants).
	 */
	protected Vector memberInvariants;

	private Vector staticConstraints;
	private Vector instanceConstraints;

	/**
	 * Accessible depends clause from this class (Vector of Depends)
	 * 
	 * @see Depends
	 **/
	transient Vector accessibleDepends;

	/** 
	 * Static invariants of the class. (Vector of 
	 * <code>jml2b.structure.Invariants</code>).
	 * 
	 * @see Invariant
	 */
	public Vector staticInvariants;

	/** 
	 * Static final fields declaration of the class. (Vector of 
	 * <code>jml2b.structure.Invariants</code>).
	 * 
	 * @see Invariant
	 */
	public Vector staticFinalFieldInvariants;

	/** 
	 * All the invariants of the class. That is, the static invariants as
	 * well as the member invariants.
	 */
	protected Vector allInvariants;

	protected Vector allConstraints;

	/**
	 * Set of depends clause.
	 * The elements contained within this vector are of type
	 * <code>Depends</code>
	 * @see Depends.
	 **/
	private Vector depends;

	/**
	 * Set of represents clause.
	 * The elements contained within this vector are of type
	 * <code>Represents</code>
	 * @see Represents. 
	 **/
	private Vector represents;

	/**
	 * Methods defined by the current class.
	 * Vector of <code>Method</code> elements.
	 * @see Method
	 */
	public Vector methods;

	/**
	 * Constructors defined by the current class.
	 * Vector of <code>Method</code> elements.
	 * @see Method
	 */
	public Vector constructors;

	/**
	 * Boolean indicating wether the class is an "external" class. An
	 * external class is a class that is defined in a different package
	 * than the package of the file whose proof obligations are generated.
	 */
	private boolean externalClass;

	private int firstLine;

	public Class() {
		
	}
	
	/** 
	 * Creates a new class in package <code>class_package</code>, with 
	 * the given modifiers. 
	 * 
	 * @param jf the file that defines the class.
	 * @param tree the AST tree corresponding to the class.
	 * @param class_package the package this class belongs to.
	 * @param mods the modifiers of this class.
	 * @param external indicate wether the class correspond to an 
	 *     "external" class, and so if the package/private fields 
	 *     must be ignored
	 */
	public Class(
		JmlFile jf,
		AST tree,
		Package class_package,
		Modifiers mods,
		boolean external) {
		super(jf, tree);
		linkedState = STATE_UNLINKED;

		fields = new Vector();
		allInvariants = new Vector();
		allConstraints = new Vector();
		depends = new Vector();
		represents = new Vector();
		implementedInterfaces = new Vector();
		methods = new Vector();
		constructors = new Vector();

		modifiers = mods;
//		if(modifiers != null && modifiers.isNative())
//			Logger.get().println(this.getName() + ": I am native");
		classPackage = class_package;
		interfaceModifier = false;
		externalClass = external;
	}


	/**
	 * Returns the default constructor for this class, if the class
	 * defines one.
	 * @return Method the default constructor or <code>null</code> if the
	 *    class does not define a default constructor. 
	 */
	public AMethod getDefaultConstructor() {
		Enumeration e = constructors.elements();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			if (m.getParams().nparams() == 0) {
				return m;
			}
		}
		return null;
	}

	/**
	 * Returns true if the current class is an "external" class. An
	 * external class is a class that is defined in a different package
	 * than the package of the file whose proof obligations are generated.
	 * 
	 * @return boolean <code>true</code> if the class is an external class, 
	 *   <code>false</code> otherwise.
	 */
	public boolean isExternal() {
		return externalClass;
	}

	/**
	 * Returns the package this class belongs to.
	 * @return Package the package this class belongs to.
	 */
	public Package getPackage() {
		return classPackage;
	}

	public boolean isInterface() {
		return interfaceModifier;
	}

	/**
	 * Returns the modifiers associated to the current class.
	 * 
	 * @return Modifiers the modifies associated to the current class.
	 */
	public IModifiers getModifiers() {
		return modifiers;
	}

	/**
	 * Returns the name of the class.
	 * 
	 * @return the name of the class.
	 */
	public String getName() {
		return name;
	}

	/**
	 * Gets the field named name if it is visible from the given class.
	 * If the field is not found in the current class, its super 
	 * classes are searched. Thus the returned field is not guaranted to
	 * be declared in the current class. 
	 * 
	 * @param name the name of the field
	 * @param from the class from wich the field should be visible.
	 * @return the field, if it is found, otherwise <code>null</code>.
	 */
	public AField getField(String name, AClass from) {
		Enumeration e = getFields();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			if (name.equals(f.getName()) && f.isVisibleFrom(from)) {
				// field found
				return f;
			}
		}
		// not found. search in implemented interfaces.
		e = getImplements();
		while (e.hasMoreElements()) {
			Type t = (Type) e.nextElement();
			AClass c = t.getRefType();

			AField f = c.getField(name, from);
			if (f != null) {
				return f;
			}
		}

		// Not found in current class. Search in superclass
		if (!isInterface() && !isObject()) {
			AClass super_class = getSuperClass();
			return super_class.getField(name, from);
		}
		return null;
	}

/**
	 * Returns an enumeration of the fields defined by the current class.
	 * The enumerated elements are of type <code>Field</code>.
	 * 
	 * Note that only the fields defined by the class are returned. Fields
	 * defined by a super class of the current class are not returned. 
	 * 
	 * @return Enumeration an enumeration of the fields defined by the
	 *     current class.
	 * @see Field
	 */
	public Enumeration getFields() {
		return fields.elements();
	}

	public Vector getFieldsV() {
		return fields;
	}

	/**
	 * Returns a vector containing all the fields defined by the current 
	 * class and its super classes.
	 * The elements stored in the vector are of type <code>Field</code>
	 * 
	 * @return Vector a vector containing all the fields defined by the
	 *     current class and its super classes.
	 * @see Field
	 */
	/*@ ensures \result != null; */
	public Vector getOwnFields() {
		Vector res = new Vector();
		Enumeration e = fields.elements();
		while (e.hasMoreElements())
			res.add(e.nextElement());
		res = getSuperClass().addSuperFields(this, res);
		return res;
	}

	/**
	 * Returns an enumeration of the invariants defined by this class.
	 * The enumerated elements are of type <code>Invariant</code>.
	 * 
	 * @return Enumeration an enumeration of the invariants.
	 * @see Invariant
	 */
	/*@ ensures \result != null; */
	public Enumeration getInvariants() {
		return allInvariants.elements();
	}

	public Enumeration getConstraints() {
		return allConstraints.elements();
	}

	/**
	 * Returns an enumeration of the static invariants defined by this 
	 * class.
	 * The enumerated elements are of type <code>Invariant</code>.
	 * 
	 * @return Enumeration an enumeration of the invariants.
	 * @see Invariant
	 */
	/*@ ensures \result != null; */
	public Enumeration getStaticInvariants() {
		//	Logger.err.println("    getStaticInvariant for: " + getName());
		return staticInvariants.elements();
	}

	/**
	 * Returns an enumeration of the represents clauses defined in this
	 * class.
	 * The enumerated elements are of type <code>Represents</code>.
	 * 
	 * @return Enumeration an enumeration of the represents clauses.
	 * @see Represents.
	 */
	/*@ ensures \result != null; */
	public Enumeration getRepresents() {
		return represents.elements();
	}

	/**
	 * Returns an enumeration of the represents clauses defined in this
	 * class.
	 * The enumerated elements are of type <code>Depends</code>.
	 * 
	 * @return Enumeration an enumeration of the depends clauses.
	 * @see Depends.
	 */
	/*@ ensures \result != null; */
	public Enumeration getDepends() {
		return depends.elements();
	}

	/**
	 * Returns an enumeration of the invariants corresponding to static
	 * final fields.
	 * The type of the enumerated elements is <code>Invariant</code>. 
	 * @return Enumeration an enumeration of the static final invariants.
	 * @see Invariant 
	 */
	/*@ ensures \result != null; */
	public Enumeration getStaticFinalFieldsInvariant() {
		return staticFinalFieldInvariants.elements();
	}

	/**
	 * Returns an enumeration of the member invariants. Member invariants
	 * are invariants that refers member variables.
	 * The returned enumeration enumerates <code>Invariant</code> 
	 * elements. 
	 * @return Enumeration an enumeration of the member invariants.
	 * @see Invariant
	 */
	/*@ ensures \result != null; */
	public Enumeration getMemberInvariants() {
		return memberInvariants.elements();
	}

	/** 
	 * Returns an enumeration of the implemented interfaces. The elements
	 * returned by the enumeration are of class <code>Type</code>.
	 *
	 * @return Enumeration the implemented interfaces.
	 */
	public Enumeration getImplements() {
		return implementedInterfaces.elements();
	}

	/**
	 * Returns an enumeration of the methods declared by the current 
	 * class.
	 * The enumerated elements are of type <code>Method</code>.
	 * 
	 * @return Enumeration an enumeration of the method declared by the
	 *     current class.
	 * @see Method
	 */
	public Enumeration getMethods() {
		return methods.elements();
	}

	/** 
	 * Searches for a method with the given name and parameters in the 
	 * current class.
	 * 
	 * Note that the method is searched only in the current class, and
	 * that the parameters must be the same (a method with same name and
	 * compatible parameters will not be returned).
	 * 
	 * @param name the name of the method
	 * @param p the parameters of the method.
	 * @return the method if it is found, <code>null</code> otherwise.
	 */
	public AMethod getMethod(IJml2bConfiguration config, String name, Parameters p) {
		Enumeration e = getMethods();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			if (m.getName().equals(name) && m.getParams().isSameAs(p)) {
				return m;
			}
		}
		return null;
	}

	public Method getConstructor(Parameters p) {
		Enumeration e = getConstructors();
		while (e.hasMoreElements()) {
			Method m = (Method) e.nextElement();
			if (m.getParams().isSameAs(p)) {
				return m;
			}
		}
		return null;
	}

	/**
	 * Returns an enumeration of the constructors defined by this class.
	 * The enumerated elements are of type <code>Method</code>.
	 * 
	 * @return Enumeration an enumeration of the constructors.
	 * @see Method
	 */
	/*@ ensures \result != null; */
	public Enumeration getConstructors() {
		return constructors.elements();
	}

	/** 
	 * Initialise the content of the class from the given AST tree.
	 * <code>tree</code> must have type <code>modifier_set</code>.
	 * 
	 * @param jmlFile the file that declares the current class.
	 * @param tree the AST corresponding to the class declaration.
	 * @return the node next after the class declaration.
	 * @throws Jml2bException in the case where a parse error occur.
	 */
	/*@ requires tree != null; */
	public AST parse(JmlFile jmlFile, AST tree) throws Jml2bException {
		AST current = tree;
		if (current == null) {
			Logger.err.println("Error : null AST encountered");
			return null;
		}

		int token_type = current.getType();
		AST children = current.getFirstChild();

		switch (token_type) {
			case LITERAL_class :
				parseClass(jmlFile, children, false);
				break;
			case LITERAL_interface :
				parseClass(jmlFile, children, true);
				break;
			default :
				throw new TokenException(
					jmlFile,
					(LineAST) current,
					"Class.parse",
					"class or interface",
					token_type);
		}

		if (constructors.isEmpty() && !isInterface()) {
			// in case where there is no constructor, add an empty one
			addDefaultConstructor();
		}

		return current.getFirstChild();
	}

	/**
	 * Link the externally visible parts of the class.
	 * 
	 * @param config the configuration that should be used.
	 * @param f the current link context.
	 */
	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (linkedState >= STATE_LINKED) {
			return;
		}

		// link the superclass.
		if (superClass == null) {
			superClass = config.getObject();
		} else if (!isObject()) {
			superClass.link(config, f);
			LinkContext superF =
				new LinkContext(superClass.getRefType());
			superF.setCurrentClass(superClass.getRefType());
			superClass.getRefType().link(config, superF);
		}

		// link each of the implemented interfaces
		LinkUtils.linkEnumeration(config, getImplements(), f);

		// link the fields
		LinkUtils.linkEnumeration(config, getFields(), f);

		// link the invariants
		LinkUtils.linkEnumeration(config, getInvariants(), f);

		LinkUtils.linkEnumeration(config, getConstraints(), f);

		// link the depends
		LinkUtils.linkEnumeration(config, getDepends(), f);

		// link the represents
		LinkUtils.linkEnumeration(config, getRepresents(), f);

		// link the methods
		LinkUtils.linkEnumeration(config, getMethods(), f);

		// link the constructors
		LinkUtils.linkEnumeration(config, getConstructors(), f);

		linkedState = STATE_LINKED;

	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (linkedState >= STATE_LINKED_TYPE_CHECKED) {
			return null;
		}

		// type check the invariants
		LinkUtils.typeCheckEnumeration(config, getInvariants(), f);
		LinkUtils.typeCheckEnumeration(config, getConstraints(), f);

		// type check the depends
		//LinkUtils.typeCheckEnumeration(config, getDepends(), f);

		// type check the represents
		LinkUtils.typeCheckEnumeration(config, getRepresents(), f);

		// type check the methods
		LinkUtils.typeCheckEnumeration(config, getMethods(), f);

		// type check the constructors
		LinkUtils.typeCheckEnumeration(config, getConstructors(), f);

		linkedState = STATE_LINKED_TYPE_CHECKED;
		return null;
	}

	/**
	 * Link the parts that cannot be directly referenced from the outside.
	 * Those parts includes statements, initialisation of fields and method
	 * body.
	 * 
	 * @param config the configuration that should be used
	 * @param f the current link context
	 * @throws Jml2bException in the case where identifier cannot be linked
	 * @throws jml2b.exceptions.InternalError
	 */
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		int errors = 0;
		if (linkedState >= STATE_LINKED_STATEMENTS) {
			// don't relink if it is already done
			return errors;
		}

		// link the superclass.
		if (superClass == null) {
			superClass = config.getObject();
		} else if (!isObject()) {
			//LB add getRefType() to realy link the statements !!!!
			LinkContext superF =
				new LinkContext(superClass.getRefType());
			superF.setCurrentClass(superClass.getRefType());
			errors += superClass.getRefType().linkStatements(config, superF);
		}

		// link each of the implemented interfaces
		errors += LinkUtils.linkStatements(config, getImplements(), f);

		// link the fields
		errors += LinkUtils.linkStatements(config, getFields(), f);

		// link the invariants
		errors += LinkUtils.linkStatements(config, getInvariants(), f);
		errors += LinkUtils.linkStatements(config, getConstraints(), f);

		// link the depends
		errors += LinkUtils.linkStatements(config, getDepends(), f);

		// link the represents
		errors += LinkUtils.linkStatements(config, getRepresents(), f);

		// separate the invariants between static invariants and member 
		// invariants

		memberInvariants = new Vector();
		staticInvariants = new Vector();

		Enumeration invariants = allInvariants.elements();
		while (invariants.hasMoreElements()) {
			Invariant i = (Invariant) invariants.nextElement();
			if (i.getModifiers().isStatic())
				staticInvariants.add(i);
			else
				memberInvariants.add(i);
		}

		instanceConstraints = new Vector();
		staticConstraints = new Vector();

		Enumeration constraints = allConstraints.elements();
		while (constraints.hasMoreElements()) {
			Constraint i = (Constraint) constraints.nextElement();
			if (i.getModifiers().isStatic())
				staticConstraints.add(i);
			else
				instanceConstraints.add(i);
		}

		staticFinalFieldInvariants = new Vector();
		addStaticFinalFieldDeclarationToInvariant();

		// link the methods
		errors += LinkUtils.linkStatements(config, getMethods(), f);

		// link the constructors
		errors += LinkUtils.linkStatements(config, getConstructors(), f);

		linkedState = STATE_LINKED_STATEMENTS;

		return errors;
	}

	/** 
	 * Parse the content of a class. tree must be a <code>INDENT</code> 
	 * node.
	 * Note that this code does not works when an interface extends
	 * multiple other interfaces.
	 * 
	 * @param jmlFile the file that defines the current class
	 * @param tree the AST corresponding to the content of the class
	 * @param is_interface boolean indicating wether the parsed class
	 *     is an interface.
	 * @throws Jml2bException
	 */
	private void parseClass(JmlFile jmlFile, AST tree, boolean is_interface)
		throws Jml2bException {
		// parse the class header

		interfaceModifier = is_interface;

		if (tree.getType() != IDENT) {
			throw new TokenException(
				jmlFile,
				(LineAST) tree,
				"Class.parseClass",
				"IDENT",
				tree.getType());
		}
		// get the name of the class
		name = tree.getText();

		// next token
		AST current = tree.getNextSibling();

		if (current.getType() == LITERAL_extends) {
			current = parseExtends(jmlFile, current);
		}

		if (current.getType() == LITERAL_implements) {
			current = parseImplements(jmlFile, current);
		}

		// now, the current node should be a LCURLY
		if (current.getType() != LCURLY) {
			throw new TokenException(
				jmlFile,
				(LineAST) current,
				"Class.parseClass",
				"LCURLY",
				current.getType());
		}

		// parse the class body
		current = current.getNextSibling();

		firstLine = ((LineAST) current).line;
		while (current != null && current.getType() != RCURLY) {
			switch (current.getType()) {
				case MODIFIER_SET :
					try {
						current = parseDeclaration(jmlFile, current);
					} catch (ParseException e) {
						//  ErrorHandler.error(jmlFile, -1, -1, e.toString());
						// print error
						Logger.err.println(e.toString());
						// advance to next
						current = current.getNextSibling();
					}
					break;
					// class or member initialiser. They don't have modifiers.
					// however, they can have requires and ensures clauses.
					// the main issue here is to handle the order of initialisation
					// for now, the initialiser is stored in the correct order in
					// the initialiser list. 
					// However, this order does not take the variable initialisers
					// into account.
					/*
					  case INIT:
					  
					  break;
					  case INSTANCE_INIT:
					  
					  break;
					*/
				default :
					//Logger.err.println("Ignoring : " + current.toString());
					current = current.getNextSibling();
					break;
			}
		}
	}

	/**
	 * Update the modifiers in case we are parsing an interface.
	 * This method adds the public and abstract flags to the modifiers for
	 * methods, and sets thepublic static final flags for variables.
	 * 
	 * @param mods the modifies
	 * @param node_type the type of node. Can be <code>METH</code> or
	 *     <code>VAR_DECL</code>.
	 */
	/*@ requires interfaceModifier == true; */
	private void fixInterfaceModifiers(Modifiers mods, int node_type) {
		switch (node_type) {
			case METH :
				// set the abstract and public flag for interfaces methods
				mods.setFlag(ModFlags.PUBLIC | ModFlags.ABSTRACT);
				break;
			case VAR_DECL :
				// a variable of an interface is implicitely 
				// public static final (excepted for ghost fields)
				if (!mods.isSet(ModFlags.GHOST)) {
					mods.setFlag(
						ModFlags.PUBLIC | ModFlags.STATIC | ModFlags.FINAL);
				} else {
					mods.setFlag(ModFlags.PUBLIC);
				}
				break;
		}
	}

	/** 
	 * Parse a declaration inside the class. A declaration can be either
	 * <ul>
	 * <li> a variable.
	 * <li> an invariant.
	 * <li> a method.
	 * <li> a constructor.
	 * <li> a depends clause.
	 * <li> a represents clause.
	 * </ul>
	 * @param jmlFile the file that declares the current class.
	 * @param a the AST corresponding to the declaration.
	 */
	private AST parseDeclaration(JmlFile jmlFile, AST a)
		throws Jml2bException {
		Modifiers mods = new Modifiers(a);
		a = a.getNextSibling();
		Declaration d;

		if (isInterface()) {
			fixInterfaceModifiers(mods, a.getType());
		}

		// in the case where we are parsing an external class, only
		// consider visible elements. This does not apply for 
		if (isExternal() && !mods.isExternalVisible()) {
			if (!classPackage.keepPackageVisible()
				|| mods.isSet(ModFlags.PRIVATE)) {
				return a.getNextSibling();
			}
		}

		switch (a.getType()) {
			case INVARIANT_KEYWORD :
				// invariant (class or instance)
				d = new Invariant(jmlFile, a.getFirstChild(), mods, this);
				d.parse(jmlFile, a.getFirstChild());
				allInvariants.add(d);
				a = a.getNextSibling();
				break;
			case CONSTRAINT_KEYWORD :
				// invariant (class or instance)
				d = new Constraint(jmlFile, a.getFirstChild(), mods, this);
				d.parse(jmlFile, a.getFirstChild());
				allConstraints.add(d);
				a = a.getNextSibling();
				break;
			case METH :
				a = parseMethod(jmlFile, a, mods, this);
				//				// method declaration
				//				d = new Method(jmlFile, a.getFirstChild(), mods, this);
				//				d.parse(jmlFile, a.getFirstChild());
				//				methods.add(d);
				//				a = a.getNextSibling();
				break;
			case VAR_DECL :
				// variable(s) declaration
				parseFields(jmlFile, a, mods);
				a = a.getNextSibling();
				break;
			case CONSTRUCTOR :
				// constructor
				d = new Constructor(jmlFile, a.getFirstChild(), mods, this);
				d.parse(jmlFile, a.getFirstChild());
				constructors.add(d);
				a = a.getNextSibling();
				break;
			case DEPENDS_KEYWORD :
				d = new Depends(jmlFile, a.getFirstChild(), mods, this);
				d.parse(jmlFile, a.getFirstChild());
				depends.add(d);
				a = a.getNextSibling();
				break;
			case REPRESENTS_KEYWORD :
				d = Represents.create(jmlFile, a.getFirstChild(), mods, this);
				d.parse(jmlFile, a.getFirstChild());
				represents.add(d);
				a = a.getNextSibling();
				break;
			case LITERAL_class :
				ErrorHandler.warning(
					jmlFile,
					((LineAST) a).line,
					((LineAST) a).column,
					"inner classes are not handled");
				a = a.getNextSibling();
				break;
			default :
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Class.parseDeclaration",
					"declaration token",
					MyToken.nodeString[a.getType()] + "(" + a.getType() + ")");
		}
		return a;
	}

	/**
	 * @param jmlFile
	 * @param a
	 * @param mods
	 * @param class1
	 * @return
	 */
	protected AST parseMethod(
		JmlFile jmlFile,
		AST a,
		Modifiers mods,
		Class class1)
		throws Jml2bException {
		Method d = new Method(jmlFile, a.getFirstChild(), mods, this);
		d.parse(jmlFile, a.getFirstChild());
		methods.add(d);
		return a.getNextSibling();
	}

	/** 
	 * Parse a field declaration.
	 * 
	 * @param jmlFile the file that declares the current class.
	 * @param a the AST corresponding to the field declaration
	 * @param mods the modifiers corresponding to the parsed field.
	 * @throws Jml2bException 
	 */
	void parseFields(JmlFile jmlFile, AST a, Modifiers mods)
		throws Jml2bException {
		VarDeclParser parser = new VarDeclParser(mods);
		parser.parse(jmlFile, a);
		Enumeration e = parser.getVars();

		// store the parsed fields into the current enumeration
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.setDefiningClass(this);
			fields.add(f);
		}
	}

	/** 
	 * Parse an extends node and the necessary siblings.
	 * <code>tree.getType()</code> must be equal to <code>LITERAL_extends</code>
	 * 
	 * @param jmlFile the file declaring the current class.
	 * @param tree the AST.
	 * @return the AST after the declaration. 
	 */
	AST parseExtends(JmlFile jmlFile, AST tree) throws Jml2bException {
		if (isInterface()) {
			AST result = tree.getNextSibling();
			parseImplementsList(jmlFile, tree.getFirstChild());
			return result;
		} else {
			tree = tree.getNextSibling();
			superClass = new Type(jmlFile, tree);
			return superClass.parse(tree);
		}
	}

	/** 
	 * Parse an implements node and the necessary siblings.
	 * 
	 * @param jmlFile the fiel declaring the current class.
	 * @param tree the AST corresponding to the declaration.
	 * @return AST the AST after the implements node. 
	 */
	AST parseImplements(JmlFile jmlFile, AST tree) throws Jml2bException {
		if (isInterface()) {
			throw new ParseException(
				jmlFile,
				(LineAST) tree,
				"Cannot have implements for interfaces");
		}
		AST childrens = tree.getFirstChild();
		parseImplementsList(jmlFile, childrens);

		return tree.getNextSibling();
	}

	void parseImplementsList(JmlFile jmlFile, AST tree) throws Jml2bException {
		int token_type = tree.getType();
		Type t;
		switch (token_type) {
			case COMMA :
				{
					AST left, right;
					left = tree.getFirstChild();
					right = left.getNextSibling();
					parseImplementsList(jmlFile, left);
					parseImplementsList(jmlFile, right);
					break;
				}
			default :
				t = new Type(jmlFile, tree);
				t.parse(tree);
				implementedInterfaces.add(t);
		}
	}

	// add the default constructor if no constructor is provided.
	protected void addDefaultConstructor() throws Jml2bException {
		Modifiers mods = new Modifiers(ModFlags.PUBLIC);
		Constructor c =
			new Constructor(new ParsedItem(getJmlFile()), mods, this);
		c.setBody(new StSkip());
		constructors.add(c);
	}

	/**
	 * Returns the new candidate method from <code>candidate</code> and *
	 * <code>new_candidate</code>.
	 */
	private AMethod getNewCandidate(
		IJml2bConfiguration config,
		AMethod candidate,
		Method new_candidate)
		throws Jml2bException {
		// the method is a candidate.
		// 1. if there was no previous candidate, then
		//    the current method becomes the new candidate
		// 2. if there was a previous candidate, then
		//    - either one of the two methods is more specialised
		//      than the other => this one becomes the new 
		//      candidate
		//    - either no method is more specialised than the
		//      other one => neither method can be called
		//      => candidate = null
		if (candidate == null) {
			// 1.
			return new_candidate;
		} else {
			IAParameters p_candidate = candidate.getParams();
			IAParameters p_new = new_candidate.getParams();

			if (p_new.isSameAs(p_candidate)) {
				// the signature are the same. This happens when looking in
				// superclasses and an overriden method has been found
				// before. => keep the original method since it is more
				// specialised.
				// => keep the same candidate
				return candidate;
			}

			// if the signature are the same, keep the one
			// that has been found first (candidate), since
			// this is the one that is the lowest in the 
			// inheritance hierarchy
			if (p_new.isCompatibleWith(config, p_candidate)) {
				// all the parameters in new_candidate are 
				// compatibles with the parameters in candidate
				// => new_candidate is more specialised => it becomes
				// the new candidate method
				return new_candidate;
			} else if (!p_candidate.isCompatibleWith(config, p_new)) {
				// new_candidate is not more specialised than candidate,
				// and candidate is not more specialised than
				// new_candidate => none of those two methods can be
				// called. reset candidate to null.
				return null;
			} else {
				return candidate;
			}
		}
	}

	/**
	 * Search for a method looking only in the current class (or interface).
	 * 
	 * @param config the configuration that should be used.
	 * @param mth_name the name of the searched method.
	 * @param param_types vector of <code>Type</code> elements containing 
	 *     the signature of the searched method.
	 * @param candidate the current best candidate method.
	 * @return the new best candidate method.
	 */
	public AMethod lookupMethodCurrentClass(
		IJml2bConfiguration config,
		String mth_name,
		Vector param_types,
		AMethod candidate)
		throws Jml2bException {
		// search in current class
		Enumeration e = getMethods();
		while (e.hasMoreElements()) {
			Method current = (Method) e.nextElement();

			if (mth_name.equals(current.getName())) {
				// the method has the same name. look for exact match
				if (current.getParams().hasSameTypes(param_types)) {
					return current;
				}
				// check if the method is a potential candidate
				if (current.getParams().isCompatible(config, param_types)) {
					candidate = getNewCandidate(config, candidate, current);
				}
			}
		}

		return candidate;
	}

	/**
	 * Returns the constructor matching the given parameter types. It use the 
	 * same lookup parameter matching strategy as the one used for methods
	 * 
	 * @param config the configuration that should be used.
	 * @param param_types vector of <code>Type</code> elements corresponding 
	 *     to the signature of the constructor.
	 * @return Constructor the searched constructor, <code>null</code> if
	 *     no such constructor could be found.
	 */
	public AMethod getConstructor(
		IJml2bConfiguration config,
		Vector param_types)
		throws Jml2bException {
		AMethod result = null;

		// search in current class
		Enumeration e = getConstructors();
		while (e.hasMoreElements()) {
			Constructor current = (Constructor) e.nextElement();

			if (current.getParams().hasSameTypes(param_types)) {
				return current;
			}
			// check if the method is a potential candidate
			if (current.getParams().isCompatible(config, param_types)) {
				result = getNewCandidate(config, result, current);
			}
		}

		return (Constructor) result;
	}

	public String getDefaultBName() {
		return "c_" + getFullyQualifiedName().replace('.','_');
	}

	/**
	 * Returns true if the current class can see the class <code>c/code>.
	 * 
	 * @param c the class that is tested for visibility.
	 * @return true if <code>c</code> is visible from the current class, 
	 *     <code>false</code> otherwise.
	 **/
	private boolean canSee(AClass c) {
		try {
			if (c.getModifiers() == null) {
				throw new InternalError(
					"canSee modifiers is null for class " + c.getName());
			}
			// we do not have to handle the "protected" case specifically, since
			// classes can be either package or public, but cannot be protected.
			return c.getPackage() == getPackage()
				|| c.getModifiers().isExternalVisible();
		} catch (NullPointerException npe) {
			Logger.err.println("NullPointerException canSee " + c.getName());
			throw npe;
		}
	}

	private Vector addGlobalStaticInvariant(AClass c) {
		Vector res = new Vector();
		// ensures that the class is visible
		if (canSee(c)) {
			Enumeration e = c.getStaticInvariants();
			while (e.hasMoreElements()) {
				Invariant i = (Invariant) e.nextElement();
				if (i.isVisibleFrom(this)) {
					res.add(i.getInvariant());
				}
			}

			e = c.getRepresents();
			while (e.hasMoreElements()) {
				Represents i = (Represents) e.nextElement();
				if (i.isVisibleFrom(this) && i.getModifiers().isStatic()) {
					res.add(i);
				}
			}

		}
		return res;
	}

	private Expression addStaticFinalFieldsInvariants(
		Expression current,
		AClass c) {
		// ensures that the class is visible
		if (canSee(c)) {
			Enumeration e = c.getStaticFinalFieldsInvariant();
			while (e.hasMoreElements()) {
				Invariant i = (Invariant) e.nextElement();
				if (i.isVisibleFrom(this)) {
					Expression tmp = i.getInvariant();
					current =
						(current != null) ? Expression.and(current, tmp) : tmp;
				}
			}
		}
		return current;
	}

	/**
	 * Adds the global static invariant of the given package and subpackage
	 */
	private Vector addGlobalStaticInvariant(Package p) {
		Vector res = new Vector();
		Enumeration e;
		// add global invariant from subpackages
		e = p.getSubPackages();
		while (e.hasMoreElements()) {
			Package subpackage = (Package) e.nextElement();
			res.addAll(addGlobalStaticInvariant(subpackage));
		}

		// add global invariants for classes contained within the package
		e = p.getClasses();

		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			res.addAll(addGlobalStaticInvariant(c));
		}

		return res;
	}

	private Expression addStaticFinalFieldsInvariants(
		Expression current,
		Package p) {
		Enumeration e;
		// add global invariant from subpackages
		e = p.getSubPackages();
		while (e.hasMoreElements()) {
			Package subpackage = (Package) e.nextElement();
			current = addStaticFinalFieldsInvariants(current, subpackage);
		}

		// add global invariants for classes contained within the package
		e = p.getClasses();

		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			current = addStaticFinalFieldsInvariants(current, c);
		}

		return current;
	}

	/**
	 * Returns the global static invariant. That is, the and of all the static 
	 * invariants visible from this class.
	 * This is done by traversing the packages, and adding the content of 
	 * static invariants that could be seen from this class.
	 * This has however the drawback of generating useless invariants (those
	 * that are not related to our class).
	 * 
	 * Note that the value returned could be null if no invariants are defined
	 * or seen.
	 */
	public Vector getGlobalStaticInvariant(JavaLoader p) {
		return addGlobalStaticInvariant(p.getRoot());
	}

	public Expression getStaticFinalFieldsInvariants(JavaLoader p) {
		return addStaticFinalFieldsInvariants(null, p.getRoot());
	}

	private Vector addAccessibleFields(Vector current, AClass c) {
		// ensures that the class is visible
		if (canSee(c)) {

			Enumeration e = c.getFields();
			while (e.hasMoreElements()) {
				AField f = (AField) e.nextElement();
				if (f.isVisibleFrom(this)
					&& !f.getModifiers().isFinal()) {
					current.add(f);
				}
			}

		}
		return current;
	}

	private void addAccessibleDepends(AClass c) {
		// ensures that the class is visible
		if (canSee(c)) {
			Enumeration e = c.getDepends();
			while (e.hasMoreElements()) {
				Depends d = (Depends) e.nextElement();
				if (d.isVisibleFrom(this)) {
					accessibleDepends.add(d);
				}
			}

		}
	}

//	private Formula addPureMethodDecl(IJml2bConfiguration config,
//		Formula current,
//		AClass c) throws Jml2bException, PogException{
//		// ensures that the class is visible
//		if (canSee(c) && c instanceof Class) {
//			Enumeration e= ((Class) c).methods.elements();
//			while (e.hasMoreElements()) {
//				Method m = (Method) e.nextElement();
//				if (m.getModifiers().isPure() && m.isPureMethodUsed()/*m.getReturnType().getTag() != Type.T_VOID*/) {
//					Expression f = (Expression) m.getNormalizedEnsures(config).clone();
//					f.old();
//					// ww represents the result of the operation call.
//					String ww = Statement.freshResult(m.getName());
//					f = f.subResult(ww);
//					QuantifiedVarForm w = new QuantifiedVarForm(
//					                    						new TerminalForm(ww),
//					                    						new TTypeForm(
//					                    							IFormToken.T_TYPE,
//					                    							m.getReturnType()),
//					                    						null);
//					Enumeration e1 = ((Parameters) m.getParams()).getParameters();
//					while (e1.hasMoreElements()) {
//						Field fi = (Field) e1.nextElement();
//						w =
//							new QuantifiedVarForm(
//								new TerminalForm(new Identifier(fi)),
//								new TTypeForm(
//									IFormToken.T_TYPE,
//									fi.getType()),
//								w);
//					}
//					Formula decl = new DeclPureMethodForm(new TerminalForm(new Identifier(m)),
//					                                      m.isStatic() ? null : 	new TTypeForm(
//					          					                    							IFormToken.T_TYPE,
//					        					                    							new Type(m.getDefiningClass())),
//					                                      w,
//					                                      ww,
//					                                      f.exprToForm(config));
//					current =
//						(current != null) ? Formula.and(current, decl) : decl;
//			}
//			}
//		}
//		return current;
//	}
	

	private Vector addAccessibleFields(Vector current, Package p) {
		Enumeration e;
		// add global invariant from subpackages
		e = p.getSubPackages();
		while (e.hasMoreElements()) {
			Package subpackage = (Package) e.nextElement();
			current = addAccessibleFields(current, subpackage);
		}

		// add global invariants for classes contained within the package
		e = p.getClasses();

		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			current = addAccessibleFields(current, c);
		}

		return current;
	}

	private void addAccessibleDepends(Package p) {
		Enumeration e;
		// add global invariant from subpackages
		e = p.getSubPackages();
		while (e.hasMoreElements()) {
			Package subpackage = (Package) e.nextElement();
			addAccessibleDepends(subpackage);
		}

		// add global invariants for classes contained within the package
		e = p.getClasses();

		while (e.hasMoreElements()) {
			AClass c = (AClass) e.nextElement();
			addAccessibleDepends(c);
		}
	}


//	private Formula addPureMethodDecl(
//			IJml2bConfiguration config,
//			Formula current,
//			Package p)
//			throws Jml2bException, PogException {
//			Enumeration e;
//			// add global invariant from subpackages
//			e = p.getSubPackages();
//			while (e.hasMoreElements()) {
//				Package subpackage = (Package) e.nextElement();
//				current = addPureMethodDecl(config, current, subpackage);
//			}
//
//			// add global invariants for classes contained within the package
//			e = p.getClasses();
//
//			while (e.hasMoreElements()) {
//				AClass c = (AClass) e.nextElement();
//				current = addPureMethodDecl(config, current, c);
//			}
//
//			return current;
//		}


	public String getFullyQualifiedName() {
		String class_name = getName();
		String pkg_name = classPackage.getFullyQualifiedName();
		if (pkg_name == null) {
			return class_name;
		} else {
			return pkg_name + "." + class_name;
		}
	}

	/** 
	 * Return true iff the class "this" is equals to the class denoted by
	 * the given fully qualified name.
	 */
	public boolean equals(String fqn) {
		return fqn.equals(getFullyQualifiedName());
	}


//	public Formula getPureMethodDecl(IJml2bConfiguration config)
//	throws Jml2bException, PogException {
//	return addPureMethodDecl(config, null, ((JavaLoader) config.getPackage()).getRoot());
//}

	public Enumeration getAccessibleDepends(JavaLoader p) {
		if (accessibleDepends == null) {
			accessibleDepends = new Vector();
			addAccessibleDepends(p.getRoot());
		}
		return accessibleDepends.elements();
	}

	public Vector getAccessibleFields(JavaLoader p) {
		return addAccessibleFields(new Vector(), p.getRoot());
	}

	
//	/**
//	 * Clear all classes that could have been instanciated.
//	 * This method is called by Package.clearAll();
//	 */
//	public static void clearAll() {
//		arrayClass = null;
//	}



	protected void addStaticFinalFieldDeclarationToInvariant() {
		Enumeration e = fields.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			if (f.isExpanded()) {
				staticFinalFieldInvariants.add(
					new Invariant(
						new BinaryExp(
							EQUALITY_OP,
							new TerminalExp(new Identifier(f)),
							"==",
							f.getAssign()),
						(Modifiers) f.getModifiers(),
						this));
			}
		}
	}

	static final long serialVersionUID = 4656487665386572390L;
	/**
	 * @return
	 */
	/**
	 * @return
	 */

	/**
	 * @param f
	 */
	public void addGhost(Field f) {
		fields.add(f);
	}

	/**
	 * @return
	 */
	public int getFirstLine() {
		return firstLine;
	}

	/**
	 * @param fi
	 */
	public void addFields(Field fi) {
		fields.add(fi);
	}

	public Vector getStaticConstraints() {
		Vector res = new Vector();
		Enumeration e = staticConstraints.elements();
		while (e.hasMoreElements()) {
			Constraint c = (Constraint) e.nextElement();
			res.add((JmlExpression) c.getInvariant().instancie().clone());
		}
		return res;
	}

	public Vector getInstanceConstraints() {
		Vector res = new Vector();
		Enumeration e = instanceConstraints.elements();
		while (e.hasMoreElements()) {
			Constraint c = (Constraint) e.nextElement();
			res.add((JmlExpression) c.getInvariant().instancie().clone());
		}
		return res;
	}
	
	public void setSuperClass(Type object) {
		superClass = object;
	}

	public void setName(String string) {
		name = string;
	}

}