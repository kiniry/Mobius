//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Method.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.java;

import jack.util.Logger;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Vector;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.TokenException;
import jml2b.formula.IModifiesField;
import jml2b.link.LinkContext;
import jml2b.link.LinkUtils;
import jml2b.link.TypeCheckable;
import jml2b.structure.AMethod;
import jml2b.structure.IAParameters;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.jml.ModifiesList;
import jml2b.structure.jml.ModifiesNothing;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.StLoops;
import jml2b.structure.statement.Statement;
import jml2b.structure.statement.TerminalExp;
import antlr.collections.AST;

/**
 * @author L. Burdy, A. Requet
 */
public class Method
	extends AMethod
	implements Serializable, IModifiesField, TypeCheckable {
	/**
	 * The content of the requires clause.
	 */
	private Expression requires;

	/**
	 * Boolean indicating wether the method is normalised or not.
	 */
	private boolean jmlNormalized = false;
	
	//private boolean coqDef = false;

	/**
	 * Body of the method.
	 */
	private Statement body;

	/**
	 * type of main specification of the method: behaviour, normal, ...
	 */
	private int specType = -1;

	/**
	 * Return type of the method.
	 */
	private Type returnType;

	/**
	 * Name of the method.
	 */
	String name;

	private Parameters signature;

	/** 
	 * Vector of types corresponding to the content of the throws clause.
	 */
	private Vector exceptions;

	/** 
	 * The line in the file where the method begin.
	 */
	protected int firstLine;

	/**
	 * The different specification cases for the method.
	 * All the elements of this vector are of type <code>SpecCase</code>.
	 */
	protected Vector specCases;

	/*@ invariant specCases != null;
	  @ invariant lemmas != null;
	  @*/

	public Method() {
		
	}
	
	public Method(JmlFile jf, AST tree, Modifiers m, Class defining)
		throws Jml2bException {
		super(jf, tree, m, defining);

		// the ABSTRACT flag is set for native methods as well as ghost 
		// ones, since those methods do not contains code (which is
		// very similar to abstract from a PO Generator point of view)
		//		if (m.isSet(ModFlags.NATIVE) || m.isSet(ModFlags.GHOST)) {
		//			m.setFlag(ModFlags.ABSTRACT);
		//		}

		signature = new Parameters();
		exceptions = new Vector();
		//		requires = new TerminalExp(MyToken.BTRUE, "(0=0)");
//		lemmas = new Proofs();
//		wellDefinednessLemmas = new Proofs();
		specCases = new Vector();
	}

	public Method(ParsedItem pi, Modifiers m, Class defining)
		throws Jml2bException {
		super(pi, m, defining);

		if (m.isSet(ModFlags.NATIVE)) {
			m.setFlag(ModFlags.ABSTRACT);
		}

		signature = new Parameters();
		exceptions = new Vector();
		//		requires = new TerminalExp(MyToken.BTRUE, "(0=0)");
//		lemmas = new Proofs();
//		wellDefinednessLemmas = new Proofs();
		specCases = new Vector();
	}

	//	public Method(
	//		String name,
	//		String pmiName,
	//		Proofs p,
	//		Proofs wellDefinednessLemmas,
	//		int line) {
	//		super(new ParsedItem(), new Modifiers(0));
	//		this.name = name;
	//		this.pmiName = pmiName;
	//		firstLine = line;
	//		lemmas = p;
	//		this.wellDefinednessLemmas = wellDefinednessLemmas;
	//		specCases = new Vector();
	//	}

	public IAParameters getParams() {
		return signature;
	}

	public String getParamsString() {
		return getParams().toString(',');
	}
	
	public Statement getBody(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		return body;
	}

	public boolean hasNoCode() {
		Modifiers m = (Modifiers) getModifiers();
		return m.isSet(ModFlags.ABSTRACT)
			|| m.isSet(ModFlags.NATIVE)
			|| m.isSet(ModFlags.GHOST);
	}

	public AST parse(JmlFile jmlFile, AST a) throws Jml2bException {
		firstLine = ((LineAST) a).line;
		// return type
		Type ret = new Type(jmlFile, a);

		// parse the type declaration
		a = ret.parse(a);

		returnType = ret;

		return parseAfterRetType(jmlFile, a);
	}

	/**
	 * Fill the given vector with the content of the spec cases corresponding 
	 * to the content of the given AST.
	 * 
	 * returns the updated <code>first_line</code> value.
	 */
	private void fillAlsoCases(
		JmlFile file,
		AST a,
		Expression current_req,
		Vector label,
		Modifiers mods,
		int type)
		throws Jml2bException {
		switch (a.getType()) {
			case ALSO :
				a = a.getFirstChild();
				fillAlsoCases(
					file,
					a,
					current_req,
					(Vector) label.clone(),
					mods,
					type);
				fillAlsoCases(
					file,
					a.getNextSibling(),
					current_req,
					label,
					mods,
					type);
				break;
			case SPEC_CASE :
				fillCasesFromContent(
					file,
					a.getFirstChild(),
					current_req,
					label,
					mods,
					type);
				break;
		}
	}

	/**
	 * Fills the given vector with all the cases corresponding to the
	 * given AST.
	 * The given AST is assumed to point to a node that is *under* 
	 * a <code>SPEC_CASE</code> node. That is, it contains the content 
	 * of the spec case (<code>REQUIRES_KEYWORD</code>, etc...)
	 */
	private void fillCasesFromContent(
		JmlFile file,
		AST a,
		Expression current_req,
		Vector labels,
		Modifiers mods,
		int type)
		throws Jml2bException {

		while (a != null && a.getType() == LABEL_KEYWORD) {
			SpecCase.parseLabel(labels, a, file);
			a = a.getNextSibling();
		}

		// parse the content of the requires clause, if any.
		while (a != null && a.getType() == REQUIRES_KEYWORD) {
			if (((LineAST) a).line < firstLine)
				firstLine = ((LineAST) a).line;
			AST child = a.getFirstChild();
			Expression req = Expression.createE(file, child);
			req.parse(child);

			if (current_req == null) {
				// if we require current_req not to be null, then, this
				// test could be avoided.
				current_req = req;
			} else {
				current_req = new BinaryExp(LOGICAL_OP, current_req, "&&", req);
			}

			a = a.getNextSibling();
		}

		SpecCase current_case = new SpecCase();

		while (a != null) {
			switch (a.getType()) {
				case LCURLY_VBAR :
					// in that case, the spec_case is subdivided into several subcases
					a = a.getNextSibling();
					// fill with the content of the cases
					fillAlsoCases(
						file,
						a,
						current_req,
						(Vector) labels.clone(),
						mods,
						type);

					// should return now, but performs some sanity checks
					a = a.getNextSibling();
					if (a.getType() != VBAR_RCURLY) {
						throw new TokenException(
							file,
							(LineAST) a,
							"fillCasesContent",
							VBAR_RCURLY,
							a.getType());
					}
					a = a.getNextSibling();
					if (a != null) {
						throw new Jml2bException("Content encountered after VBAR_RCURLY");
					}
					return;
				case SIG_SEQ :
					//					if (current_case == null) {
					//						current_case =
					//							new SpecCase(
					//								file.getConfig(),
					//								current_req,
					//								labels,
					//								mods,
					//								type);
					//					}
					firstLine =
						current_case.parseExsures(
							file,
							a.getFirstChild(),
							firstLine);
					break;
				case ENS_SEQ :
					//					if (current_case == null) {
					//						current_case =
					//							new SpecCase(
					//								file.getConfig(),
					//								current_req,
					//								labels,
					//								mods,
					//								type);
					//					}
					firstLine =
						current_case.parseEnsures(
							file,
							a.getFirstChild(),
							firstLine);

					break;
				case ASGNABLE_SEQ :
					//					if (current_case == null) {
					//						current_case =
					//							new SpecCase(
					//								file.getConfig(),
					//								current_req,
					//								labels,
					//								mods,
					//								type);
					//					}
					// modifies
					firstLine =
						current_case.parseModifies(
							file,
							a.getFirstChild(),
							firstLine);
					break;
				case DIV_SEQ :
					// currently ignored
					break;
				default :
					Logger.err.println(
						"Method.fillCasesFromContent: token "
							+ a.getType()
							+ " encountered");
			}
			a = a.getNextSibling();
		}

		if (current_case != null) {
			//			if ((type == SpecCase.LIGHTWEIGHT_CASE
			//				|| type == SpecCase.DEFAULT_BEHAVIOR_CASE)
			//				&& !current_case.hasExsures()) {
			//				current_case.addDefaultExsures();
			//			}
			//
			current_case.completeSpecCase(
				file.getConfig(),
				current_req,
				labels,
				mods,
				(Modifiers) getModifiers(),
				type);

			// add the case to the list of spec_cases
			specCases.add(current_case);
		}
	}

	/**
	 * Parse the header part of a spec case. That is, the privacy 
	 * and behavior modifiers.
	 * 
	 * If get_requires is true, the content of the requires clause is
	 * anded with the requires of the method to construct the global
	 * requires of the method.
	 */
	/*@
	  @ requires a.getType() == SPEC_CASE;
	  @*/
	private void parseBehaviorSpec(JmlFile file, AST a, boolean get_requires)
		throws Jml2bException {
		Modifiers mods = null;
		// the type of the case (defaults to lightweight).
		int type = SpecCase.LIGHTWEIGHT_CASE;

		a = a.getFirstChild();

		if (a.getType() == PRIVACY_MODIFIER) {
			mods = new Modifiers(a);
			if (((LineAST) a).line < firstLine && ((LineAST) a).line != 0)
				firstLine = ((LineAST) a).line;

			a = a.getNextSibling();
		}

		switch (a.getType()) {
			case NORMAL_BEHAVIOR :
				type = SpecCase.NORMAL_BEHAVIOR_CASE;
				if (((LineAST) a).line < firstLine)
					firstLine = ((LineAST) a).line;
				a = a.getNextSibling();
				break;
			case EXCEPTIONAL_BEHAVIOR :
				type = SpecCase.EXCEPTIONAL_BEHAVIOR_CASE;
				if (((LineAST) a).line < firstLine)
					firstLine = ((LineAST) a).line;
				a = a.getNextSibling();
				break;
			case BEHAVIOR :
				type = SpecCase.DEFAULT_BEHAVIOR_CASE;
				if (((LineAST) a).line < firstLine)
					firstLine = ((LineAST) a).line;
				a = a.getNextSibling();
				break;
		}

		if (a.getType() != SPEC_CASE) {
			Logger.err.println("Method.parseBehaviorSpec: unexpected token");
			throw new TokenException(
				file,
				(LineAST) a,
				"Method.parseBehaviorSpec",
				SPEC_CASE,
				a.getType());
		}

		a = a.getFirstChild();

		Vector label = new Vector();

		if (get_requires) {
			while (a != null && a.getType() == LABEL_KEYWORD) {
				SpecCase.parseLabel(label, a, file);
				a = a.getNextSibling();
			}

			while (a != null && a.getType() == REQUIRES_KEYWORD) {
				if (((LineAST) a).line < firstLine)
					firstLine = ((LineAST) a).line;
				AST child = a.getFirstChild();
				Expression req = Expression.createE(file, child);
				req.parse(child);
				if (requires == null)
					requires = req;
				else
					requires = new BinaryExp(LOGICAL_OP, requires, "&&", req);

				a = a.getNextSibling();
			}
		}

		fillCasesFromContent(file, a, null, label, mods, type);
		if (specType == -1)
			specType = type;
	}

	/**
	 * Parses the content of a specification containing ALSO nodes.
	 */
	private void parseAlsoSpec(JmlFile file, AST a) throws Jml2bException {
		AST tmp;

		switch (a.getType()) {
			case ALSO :
				tmp = a.getFirstChild();
				parseAlsoSpec(file, tmp);
				parseAlsoSpec(file, tmp.getNextSibling());
				break;
			case SPEC_CASE :
				parseBehaviorSpec(file, a, false);
				break;
		}
	}

	/**
	 * Parses the specification part of the method, and returns an AST 
	 * corresponding to the next relevant part of the specification.
	 * <code>SpecCase</code> elements corresponding to the parsed specification
	 * are added to the <code>specCases</code> vector.
	 * <p>
	 * In case of a lightweight specification, the requires part of the 
	 * specification is used for the global requires of the method, and 
	 * a <code>SpecCase</code> with <code>requires true</code> contains the
	 * ensures and exsures part of the specification.
	 * <p>
	 * In case of multiple behavior, the global requires is set to true, 
	 * and at least a <code>SpecCase</code> element is created for each 
	 * behavior.
	 * <p>
	 * 
	 */
	AST parseSpec(JmlFile file, AST a) throws Jml2bException {
		// if a JML specification is associated to the method, parse it.
		switch (a.getType()) {
			case SPEC_CASE :
				parseBehaviorSpec(file, a, true);
				return a.getNextSibling();
				//case AND:
			case ALSO :
				parseAlsoSpec(file, a);
				return a.getNextSibling();

			case EXT_ALSO :
				// ignores the EXT_KEYWORD
				// assumes that 
				//   a.getType() == EXT_AND || a.getType() == EXT_ALSO
				//   ==>
				//   a.getFirstChild().getType() == SPEC_CASE ||
				//   a.getFirstChild().getType() == ALSO
				// (which in fact, is totally wrong, since EXT_AND will provides
				//  CONJOINABLE_SPEC and AND. The actual content of those AST is
				//  however very similar).
				parseSpec(file, a.getFirstChild());
				return a.getNextSibling();

			case EXT_AND :
				Logger.err.println(
					"Warning: skipping and keyword (not implemented)");
				return a.getNextSibling();
		}
		// no JML specification
		// => adds a default SpecCase with exsures (RuntimeException) false

		//		SpecCase c = new SpecCase(null, getModifiers(), SpecCase.LIGHTWEIGHT_CASE);
		//		c.addExsuresFalse("java.lang.RuntimeException");
		//		specCases.add(c);

		return a;
	}

	/**
	 * Parse after the return type declaration. This method is separated
	 * from the <code>parse</code> method in order to allow parsing 
	 * constructors without too much changes.
	 * <p>
	 * This method currently does not parse the <code>and</code> 
	 * specification keyword correctly.
	 */
	protected AST parseAfterRetType(JmlFile jmlFile, AST a)
		throws Jml2bException {
		// get the name of the method
		if (a.getType() != IDENT) {
			throw new TokenException(
				jmlFile,
				(LineAST) a,
				"Method.parseAfterRetType",
				"IDENT",
				a.getType());
		}

		// change the parsed item to point to the method name.
		change(new ParsedItem(jmlFile, a));
//		if (a.getText().startsWith("Coq__")) {
//		name = a.getText().substring(5);
//		coqDef = true;
//		}
//		else {
		name = a.getText();
//		}
		a = a.getNextSibling();

		// parse the signature
		a = signature.parse(jmlFile, a);

		// parse the throws clause, if any
		if (a.getType() == LITERAL_throws) {
			a = a.getNextSibling();
			parseThrows(jmlFile, a);
			a = a.getNextSibling();
		}

		a = parseSpec(jmlFile, a);

		// SEMI correspond to abstract methods => no body
		if (a.getType() != SEMI) {
			// ignore the body of the methods of external classes
			if (((Class) getDefiningClass()).isExternal()) {
				return null;
			}
			body = Statement.createS(jmlFile, a);
			a = body.parse(a);
		} else {
			a = a.getNextSibling();
		}

		return a;
	}

	protected void createBody(JmlFile jmlFile, AST a) throws Jml2bException {
		body = Statement.createS(jmlFile, a);
	}

	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		f.currentMethod = this;

		// link return type and signature.
		if (returnType != null) {
			returnType.link(config, f);
		}

		if (signature != null) {
			signature.link(config, f);
		}

		// add the parameters to the local variables.
		f.linkVars.pushVars();
		f.linkVars.add(signature.getSignature());

		if (requires != null) {
			requires.link(config, f);
		}

		/* link each of the spec case */
		LinkUtils.linkEnumeration(config, specCases.elements(), f);

		if (body != null) {
			body.link(config, f);
		}
		if (exceptions != null) {
			LinkUtils.linkEnumeration(config, exceptions.elements(), f);
		}

		f.currentMethod = null;
		// remove the parameters from context
		f.linkVars.popVars();
	}

	private boolean linkBodyNeeded() {
		return !((Class) getDefiningClass()).isExternal();
	}

	/*@ ensures !specCases.isEmpty(); */
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		int errors = 0;

		f.currentMethod = this;

		// link return type and signature.
		if (returnType != null) {
			errors += returnType.linkStatements(config, f);
		}

		if (signature != null) {
			errors += signature.linkStatements(config, f);
		}

		// add the parameters to the local variables.
		f.linkVars.pushVars();
		f.linkVars.add(signature.getSignature());

		if (requires != null) {
			requires.linkStatements(config, f);
			if (specCases.isEmpty()) {
				SpecCase tmp = new SpecCase(config, (Modifiers) getModifiers());
				// 
				tmp.link(config, f);
				errors += tmp.linkStatements(config, f);
				// no speccase specification given for the current method, the
				// method cannot inherit a specification from an ancestor. 
				// Adds a default specification before falling through the
				// general case where a specification has been given.
				//tmp.completeModifies();
				specCases.add(tmp);

			}
		} else {
			if (specCases.isEmpty()) {
				AMethod super_m = getSuperMethod(config);
				if (super_m == null) {
					specCases.add(new SpecCase(config, f));
				} else {
					requires =
						(super_m.getRequires() != null)
							? ((Method) super_m).getClonedRequires(this).renameParam(
								(Parameters) super_m.getParams(),
								signature)
							: null;
					specCases = super_m.getClonedSpecCases(this);
					Enumeration e = specCases.elements();
					while (e.hasMoreElements()) {
						SpecCase element = (SpecCase) e.nextElement();
						try {
							element.renameParam(
								config,
								(Parameters) super_m.getParams(),
								signature);
						} catch (PogException pe) {
							throw new Jml2bException(pe.getMessage());
						}
					}
				}
			}
		}

		errors += LinkUtils.linkStatements(config, specCases.elements(), f);

		if (body != null && linkBodyNeeded()) {
			errors += body.linkStatements(config, f);
		}
		if (exceptions != null) {
			errors
				+= LinkUtils.linkStatements(config, exceptions.elements(), f);
		}

		f.currentMethod = null;
		// remove the parameters from context
		f.linkVars.popVars();
		return errors;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		f.currentMethod = this;

		// add the parameters to the local variables.
		f.linkVars.pushVars();
		f.linkVars.add(signature.getSignature());

		if (requires != null) {
			requires.typeCheck(config, f);
		}

		/* link each of the spec case */
		LinkUtils.typeCheckEnumeration(config, specCases.elements(), f);

		if (body != null) {
			body.typeCheck(config, f);
		}

		f.currentMethod = null;

		// remove the parameters from context
		f.linkVars.popVars();
		return null;

	}

	public Type getReturnType() {
		return returnType;
	}

	public String getName() {
		return name;
	}

	// return true if this method represents a constructor.
	public boolean isConstructor() {
		return false;
	}

	public boolean isStatic() {
		return getModifiers().isStatic();
	}
	
	boolean isJmlNormalized() {
		return jmlNormalized;
	}

	protected void parseThrows(JmlFile jmlFile, AST a) throws Jml2bException {
		switch (a.getType()) {
			case COMMA :
				{
					AST ex_types = a.getFirstChild();
					parseThrows(jmlFile, ex_types);
					parseThrows(jmlFile, ex_types.getNextSibling());
					break;
				}
			default :
				{
					Type t = new Type(jmlFile, a);
					t.parse(a);
					exceptions.add(t);
					break;
				}
		}
	}

	void setBody(Statement b) {
		body = b;
	}

	void setName(String n) {
		name = n;
	}

	public String toString() {
		return ((Class) getDefiningClass()).getName()
			+ "."
			+ getName()
			+ "("
			+ signature.toString()
			+ ")";
	}

	private String pmiName;

	public String getPmiName() {
		return pmiName;
	}

	public void setPmiName(String n) {
		pmiName = n;
	}
	
	public AMethod getSuperMethod(IJml2bConfiguration config) {
		AMethod m;
		if (getModifiers().isStatic()) {
			// static methods do not inherit behavior from methods with 
			return null;
		}
		AClass c = ((Class) getDefiningClass());
		while (!c.isObject()) {
			c = c.getSuperClass();
			if ((m = c.getMethod(config, name, signature)) != null) {
				IModifiers mods = m.getModifiers();
				if (mods.isStatic()) {
					// the method found is a static method that happen
					// to have the same name and signature => not the method
					// we are looking for.
					continue;
				}
				return m;
			}
		}
		return null;
	}

	Expression normalizedRequires;

	public Expression getNormalizedRequires(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		return normalizedRequires;
	}

	public Expression getNormalizedEnsures(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		Expression res = null;
		Enumeration e = getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase sc = (SpecCase) e.nextElement();
			Expression tmp = sc.getNormalizedEnsures();
			if (res == null)
				res = tmp;
			else
				res = new BinaryExp(LOGICAL_OP, res, "||", tmp);
		}
		if (res == null)
			return new TerminalExp(MyToken.BTRUE, "(0=0)");
		else
			return res;
	}

	public Expression getExsuresAsExpression(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		Expression res = null;
		Enumeration e = getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase sc = (SpecCase) e.nextElement();
			Expression tmp = sc.getExsuresAsExpression();
			if (res == null)
				res = tmp;
			else
				res = new BinaryExp(LOGICAL_OP, res, "||", tmp);
		}
		if (res == null)
			return new TerminalExp(MyToken.BTRUE, "(0=0)");
		else
			return res;
	}

	public Expression getEnsuresAsExpression(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		Expression res = null;
		Enumeration e = getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase sc = (SpecCase) e.nextElement();
			Expression tmp = sc.getNormalizedEnsures();
			if (res == null)
				res = tmp;
			else
				res = new BinaryExp(LOGICAL_OP, res, "||", tmp);
		}
		if (res == null)
			return new TerminalExp(MyToken.BTRUE, "(0=0)");
		else
			return res;
	}

	/**
	 * Normalize the current method.
	 * Ensures that <code>processIdent</code> and <code>instancie</code> are 
	 * called for each of the element within the method.
	 * <p>
	 * Then, the normalized requires, ensures and exsures are defined as follows:
	 * <ul>
	 * <li>If the method has a specification, the normalized ensures, exsures and
	 *     requires correspond to this specification
	 * <li>If the method does not have a specification of its own, and it can 
	 *     inherit one from an ancestor, the normalized ensures exsures and 
	 *     requires correspond to the ones from its ancestor.
	 * <li>If the method does not have a specification of its own and cannot 
	 *     inherit a specification, then the normalized spec will be:
	 *     <pre>
	 *     requires true;
	 *     ensures true;
	 *     exsures (RuntimeException) false;
	 *     </pre>
	 * </ul>
	 */
	void jmlNormalize(IJml2bConfiguration config)
		throws Jml2bException, PogException {

		signature.processIdent();

		if (requires != null) {
			requires.processIdent();
			requires = (Expression) requires.instancie();
		}

		if (body != null) {
			body = (Statement) body.jmlNormalize(config, (Class) getDefiningClass());
		}

		Expression req = null;

		Enumeration e = specCases.elements();
		while (e.hasMoreElements()) {
			SpecCase element = (SpecCase) e.nextElement();
			element.jmlNormalize(config, (Class) getDefiningClass());
			if (req == null) {
				req = element.getRequires();
			} else {
				req =
					new BinaryExp(LOGICAL_OP, req, "||", element.getRequires());
			}
		}
		if (requires == null)
			normalizedRequires = req;
		else
			normalizedRequires = new BinaryExp(LOGICAL_OP, requires, "&&", req);

		jmlNormalized = true;
	}

	String getFullyQualifiedName() {
		return ((Class) getDefiningClass()).getFullyQualifiedName() + "." + name;
	}

	static final long serialVersionUID = -5486363294234267483L;

	/**
	 * Returns the specCases elements.
	 * @return Enumeration
	 */
	public Enumeration getSpecCases(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		return specCases.elements();
	}

	/**
	 * Returns the specCases.
	 * @return Vector
	 */
	public Vector getSpecCasesV(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (!jmlNormalized)
			jmlNormalize(config);
		return specCases;
	}

	private Expression getClonedRequires(ParsedItem pi) {
		Expression e = (Expression) requires.clone();
		e.setParsedItem(pi);
		return e;
	}

	public Vector getClonedSpecCases(ParsedItem pi) {
		Vector v = new Vector();
		Enumeration e = specCases.elements();
		while (e.hasMoreElements()) {
			SpecCase sc = (SpecCase) e.nextElement();
			SpecCase sc1 = (SpecCase) sc.clone();
			sc1.setParsedItem(pi);
			v.add(sc1);
		}
		return v;
	}

	/**
	 * @param line
	 * @return
	 */
	public StLoops getLoopAtLine(int line) {
		return body.getLoopAtLine(line);
	}
	public boolean matchWith(IJml2bConfiguration config, Method m)
		throws Jml2bException {
		return getName().equals(m.getName())
			&& signature.isCompatibleWith(config, m.signature);
	}

	public void addAnnotation(
		IJml2bConfiguration config,
		Expression req,
		SpecCase sc)
		throws Jml2bException, PogException {
		if (!isJmlNormalized())
			jmlNormalize(config);
		if (requires == null) {
			requires = req;
		} else if (requires.isBTrue()) {
			requires = req;
		} else if (!req.isBTrue()) {
			requires = requires.addInConjonction(req);
		}
		if (specCases.size() == 0) {
			specCases.add(sc);
		} else {
			Enumeration e = specCases.elements();
			while (e.hasMoreElements()) {
				SpecCase element = (SpecCase) e.nextElement();
				element.addAnnotation(config, sc);
			}
		}
		annotatedPrecondition.add(req);
		annotatedPostcondition.add(sc.getEnsures());
		annotatedModifies.addAll(sc.getModifies().getFields());
		isAnnotated = ALREADY_ANNOTATED;
	}

	public boolean addAnnotation(
		IJml2bConfiguration config,
		Expression req,
		Expression ens,
		ModifiesClause mod)
		throws Jml2bException, PogException {
		boolean added = false;
		if (!isJmlNormalized())
			jmlNormalize(config);
		if (req != null)
			if (requires == null) {
				requires = req;
				added = true;
			} else if (requires.isBTrue()) {
				requires = req;
				added = true;
			} else if (!req.isBTrue()) {
				Expression newRequires = requires.addInConjonction(req);
				if (newRequires != requires)
					requires = newRequires;
				else
					added = false;
			}
		if (ens != null || mod != null)
			if (specCases.size() == 0) {
				specCases.add(new SpecCase(ens, mod));
				added = true;
			} else {
				Enumeration e = specCases.elements();
				while (e.hasMoreElements()) {
					SpecCase element = (SpecCase) e.nextElement();
					added = element.addAnnotation(config, ens, mod) || added;
				}
			}
		return added;
	}

	/**
	 * @return
	 */
	public int getFirstLine() {
		return firstLine;
	}

	/**
	 * @return
	 */
	public Expression getRequires() {
		return requires;
	}

	private static final int NOT_ANNOTATED = 0;
	private static final int ALREADY_ANNOTATED = 1;

	private int isAnnotated = NOT_ANNOTATED;
	Vector annotatedPrecondition = new Vector();
	Vector annotatedPostcondition = new Vector();
	HashSet annotatedModifies = new HashSet();

	public boolean addComputedModifies(
		IJml2bConfiguration config,
		ModifiesList ml)
		throws Jml2bException, PogException {
		//		Vector fileUpdates = new Vector();
		boolean added = false;
		if (specCases.size() == 0) {
			SpecCase sc = new SpecCase();
			sc.addComputedModifies(config, ml);
			specCases.add(sc);
			added = true;
		} else {
			Enumeration e = specCases.elements();
			while (e.hasMoreElements()) {
				SpecCase element = (SpecCase) e.nextElement();
				added = element.addComputedModifies(config, ml) || added;
			}
		}
		return getFirstLine() != 0 && added;
		//		if (getFirstLine() != 0 && added)
		//			fileUpdates.add(
		//				new ReplaceFileUpdate(
		//					getJmlFile().getFileName(),
		//					emitSpecCase(config),
		//					getFirstLine() - 1));
		//		return fileUpdates;
	}

	public boolean addComputedRequires(
		IJml2bConfiguration config,
		Expression r)
		throws Jml2bException, PogException {
		//		Vector fileUpdates = new Vector();
		boolean added = true;
		if (requires == null)
			requires = r;
		else if (requires.isBTrue())
			requires = r;
		else if (!r.isBTrue()) {
			Expression newRequires = requires.addInConjonction(r);
			if (newRequires != requires)
				requires = newRequires;
			else
				added = false;
		} else
			added = false;
		return getFirstLine() != 0 && added;
		//		if (getFirstLine() != 0 && added)
		//			fileUpdates.add(
		//				new ReplaceFileUpdate(
		//					getJmlFile().getFileName(),
		//					emitSpecCase(config),
		//					getFirstLine() - 1));
		//		return fileUpdates;
	}

	public boolean isAnnotated() {
		return isAnnotated != NOT_ANNOTATED;
	}

	public Vector getAnnotatedPrecondition() {
		return annotatedPrecondition;
	}

	public HashSet getAnnotatedModifies() {
		return annotatedModifies;
	}

	public Vector getAnnotatedPostcondition() {
		return annotatedPostcondition;
	}

	/**
	 * @return
	 */
	public int getSpecType() {
		return specType;
	}

	/**
	 * @return
	 */
	public ModifiesClause getDefaultLoopModifies() {
		if (specCases.size() == 1)
			return ((SpecCase) specCases.get(0)).getModifies();
		else
			return new ModifiesNothing();
	}

	/**
	 * @param expression
	 */
	public void setRequires(Expression expression) {
		requires = expression;
	}

	/**
	 * @param vector
	 */
	public void setSpecCases(Vector vector) {
		specCases = vector;
	}

	/**
	 * @return
	 */
	public Enumeration getCalledMethods() {
		Vector calledMethod = new Vector();
		if (body != null)
			body.collectCalledMethod(calledMethod);
		return calledMethod.elements();
	}

	public String getSignature() {
		return signature.toJava();
	}
	

	public void setReturnType(Type returnType) {
		this.returnType = returnType;
	}
	
	/**
	 * Returns true if the given method has exactly the same signature as the
	 * given vector of types.
	 * 
	 * @param candidate the candidate method.
	 * @param param_types a vector of <code>Type</code> elements corresponding
	 *     to the wanted signature.
	 * @return boolean true if the signature of the candidate method is the 
	 *     same as the <code>param_type</code> vector.
	 */
	public boolean exactMatch(IJml2bConfiguration config, Vector param_types) {
		return getParams().hasSameTypes(param_types);
	}

	public boolean isCoqDef() {
		return getModifiers().isNative();//coqDef;
	}


}
