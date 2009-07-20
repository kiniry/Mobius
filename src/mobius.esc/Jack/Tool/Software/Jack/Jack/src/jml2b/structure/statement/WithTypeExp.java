//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: WithTypeExp.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.TypeCheckException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.substitution.SubArrayElement;
import jml2b.pog.substitution.SubArrayLength;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.substitution.SubInstancesSet;
import jml2b.pog.substitution.SubInstancesSingle;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.pog.substitution.SubTypeofSet;
import jml2b.pog.substitution.SubTypeofSingle;
import jml2b.pog.util.ColoredInfo;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a list of dimension corresponding to an array creation.
 * @author L. Burdy, A. Requet
 **/
class DimExpr extends ParsedItem implements IFormToken {

	/**
	 * The current dimension
	 **/
	/*@ non_null */
	private Expression exp;

	/**
	 * The next element of the list
	 **/
	private DimExpr next;

	/**
	 * Constructs a list as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	DimExpr(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		exp = Expression.createE(getJmlFile(), tree.getNextSibling());
		AST subtree = exp.parse(tree.getNextSibling());
		if (subtree != null) {
			next = new DimExpr(getJmlFile(), subtree);
		}
	}

	String toJava(int indent) {
		String s = "[" + exp.toJava(indent) + "]";
		if (next != null)
			s += next.toJava(indent);
		return s;
	}

	/**
	 * Tests whether two lists are equal
	 * @return <code>true</code> if the current expressions of the list are 
	 * equal and if the tail of the lists are equal too, <code>false</code> 
	 * otherwise
	 **/
	boolean equals(DimExpr d) {
		return exp.equals(d.exp)
			&& (next == null ? d.next == null : next.equals(d.next));
	}

	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		exp.linkStatement(config, f);
		if (next != null)
			next.linkStatement(config, f);
		return null;
	}

	/**
	 * Collects all the indentifier of the list to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	void processIdent() {
		exp.processIdent();
		if (next != null)
			next.processIdent();
	}

	/**
	 * Returns the set of parsed items that correspond to this list
	 * @return the set of parsed item that correspond to all the expression of  
	 * the list 
	 **/
	Vector getParsedItems() {
		Vector res = exp.getParsedItems();
		if (next != null)
			res.addAll(next.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		exp.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
		change(pi);
	}

	/**
	 * Calculates the proof resulting from the evaluation of each dimension
	 * expression
	 * @param config The current configuration
	 * @param length The set of temporary variable representing each dimension
	 * @param normalProof theorems to ensure if the evaluation terminates
	 * normally
	 * @param exceptionalBehaviour exceptional theorems to ensure if the
	 * evaluation terminates abruply on an exception
	 **/
	Proofs newArrayLength(
		IJml2bConfiguration config,
		Vector length,
		Proofs normalProof,
		ExceptionalBehaviourStack exceptionalProof)
		throws Jml2bException, PogException {
		String vv = (String) length.remove(0);
		Proofs t;
		Proofs u =
			exceptionalProof.throwException(
				config,
				Statement.negativeArraySizeException);

		if (next == null) {
			t = normalProof;
		} else {
			t =
				next.newArrayLength(
					config,
					length,
					normalProof,
					exceptionalProof);
		}
		Formula s =
			new BinaryForm(Ja_LE_OP, new TerminalForm(0), new TerminalForm(vv));
		u.addHyp(
			Formula.not(s),
			new ColoredInfo(exp, ColoredInfo.IS_NEGATIVE),
			VirtualFormula.LOCALES);
		t.addHyp(s, new ColoredInfo(exp), VirtualFormula.LOCALES);
		t.addAll(u);
		return exp.wp(config, vv, t, exceptionalProof);
	}

	/**
	 * Returns the next element of the list.
	 * @return <code>next</code>
	 */
	DimExpr getNext() {
		return next;
	}

	static final long serialVersionUID = -1280076634546293684L;

	/**
	 * @return
	 */
	public DimExpr instancie() {
		exp = (Expression) exp.instancie();
		if (next != null)
			next = next.instancie();
		return this;
	}
	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

}

/**
 * This class implements expression with type, that is object and array
 * creation, casting and <code>instanceof</code>. It contains a type and
 * optionnaly an expression or dimensions for array creation. It corresponds to:
 * <UL>
 * <li> <code>new t(e)</code> the expression is optionnal.
 * <li> <code>new t[e1][e2]...[en]</code>
 * <li> <code>(t) e</code>
 * <li> <code>e instanceof t<code>
 * </UL>
 * @author L. Burdy
 **/
public class WithTypeExp extends Expression {

	/**
	 * Return the normal behaviour where the result variable has been casted 
	 * into a builtin type.
	 * @param desType The buitlin type in which the result variable is casted.
	 * @param srcType The builtin type of the result variable
	 * @param f The result variable to cast
	 * @return the the normal behaviour where the result variable has been
	 * substituted with a formula that can be itself if the cast does not change
	 * the result variable (for instance byte into int), the j_xxx2yyy funtions 
	 * applicated to the result variable if the cast is performed.
	 **/
	private static Proofs cast(
		Type destType,
		Type srcType,
		String resultingVar,
		Proofs normalBehaviour) {
		Formula casted =
			cast(destType, srcType, new TerminalForm(resultingVar));
		return normalBehaviour.sub(new SubTmpVar(resultingVar, casted));
	}

	/**
	 * Cast a formula into a builtin type.
	 * @param desType The buitlin type in which the formula is casted.
	 * @param srcType The builtin type of the formula
	 * @param f The formula to cast
	 * @return the casted formula that can be itself if the cast does not 
	 * change the formula (for instance byte into int), the j_xxx2yyy funtions 
	 * applicated to the formula if the cast is performed.
	 **/
	private static Formula cast(Type destType, Type srcType, Formula f) {
		switch (destType.getTag()) {
			case Type.T_BOOLEAN :
				return f;
			case Type.T_INT :
				if (srcType.getTag() == Type.T_BYTE
						|| srcType.getTag() == Type.T_SHORT
						|| srcType.getTag() == Type.T_CHAR
						|| srcType.getTag() == Type.T_INT)
				return f;
			case Type.T_LONG :
				if (srcType.getTag() == Type.T_BYTE
						|| srcType.getTag() == Type.T_SHORT
						|| srcType.getTag() == Type.T_CHAR
						|| srcType.getTag() == Type.T_INT
						|| srcType.getTag() == Type.T_LONG)
				return f;
				
			case Type.T_CHAR :
				if (srcType.getTag() == Type.T_CHAR)
					return f;
				else
					return Formula.apply(TerminalForm.$int2char, f);

			case Type.T_SHORT :
				if (srcType.getTag() == Type.T_BYTE
					|| srcType.getTag() == Type.T_SHORT)
					return f;
				else
					return Formula.apply(TerminalForm.$int2short, f);

			case Type.T_BYTE :
				if (srcType.getTag() == Type.T_BYTE)
					return f;
				else
					return  Formula.apply(TerminalForm.$int2byte, f);
		}
		throw new jml2b.exceptions.InternalError(
			"WithTypeExp.cast: Impossible cast "
				+ srcType.getTag()
				+ " --> "
				+ destType.getTag());
	}

	/**
	 * Returns the formula corresponding to the default array element 
	 * initializer
	 * @param t The type of the element of the array
	 * @return
	 * <UL>
	 * <li> <code>false</code> for boolean array
	 * <li> <code>0</code> for integer array
	 * <li> <code>null</code> for reference array
	 * </UL>
	 **/
	public static Formula getDefaultArrayInitialiser(Type t) {
		Formula initialiser;
		// get appropriate initialiser 
		switch (t.getTag()) {
			case Type.T_BOOLEAN :
				initialiser = Formula.$false;
				break;
			case Type.T_INT :
			case Type.T_SHORT :
			case Type.T_BYTE :
			case Type.T_CHAR :
			case Type.T_LONG :
				initialiser = new TerminalForm(0);
				break;
			case Type.T_DOUBLE :
			case Type.T_FLOAT :
				initialiser = new TerminalForm(0);
				break;
			case Type.T_REF :
			case Type.T_ARRAY :
				initialiser = Formula.$null;
				break;
			default :
				throw new InternalError(
					"Unhandled case in getDefaultArrayInitialiser: "
						+ t.getTag());
		}
		return initialiser;
	}

	/**
	 * The type used in the expression. It cannot be null.
	 **/
	private Type type;

	/*@
	  @ invariant parsed ==> type != null;
	  @*/

	/**
	 * The expression can be
	 * <UL>
	 * <li> the parameter of a constructor call
	 * <li> an array intialiazer
	 * <li> a casted expression
	 * <li> a tested with <code>instanceof</code> expression
	 * </UL>
	 **/
	private Expression exp;

	/**
	 * The dimensions of created arrays.
	 **/
	private DimExpr dim;

	/**
	 * The identifier corresponding to the called constructor. It is only valid
	 * for an object created and is evaluated during the link.
	 **/
	private Identifier ident;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected WithTypeExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an expression with type form another expression with type.
	 * @param nodeType The node type
	 * @param nodeText The node text
	 * @param type The type corresponding to this expression
	 * @param exp The sub expression
	 **/
	/*@
	  @ requires exp != null;
	  @*/
	WithTypeExp(int nodeType, String nodeText, Type type, Expression exp) {
		super(nodeType, nodeText);
		this.type = type;
		this.exp = exp;
		//@ set parsed = true;
	}

	public Object clone() {
		WithTypeExp res =
			new WithTypeExp(
				getNodeType(),
				getNodeText(),
				type,
				exp == null ? null : (Expression) exp.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& type.equals(((WithTypeExp) e).type)
			&& (exp == null
				? ((WithTypeExp) e).exp == null
				: (((WithTypeExp) e).exp != null
					&& exp.equals(((WithTypeExp) e).exp)))
			&& (dim == null
				? ((WithTypeExp) e).dim == null
				: (((WithTypeExp) e).dim != null
					&& dim.equals(((WithTypeExp) e).dim)))
			&& (ident == null
				? ((WithTypeExp) e).ident == null
				: (((WithTypeExp) e).ident != null
					&& ident.equals(((WithTypeExp) e).ident)));
	}

	/**
	 * Object and array creations are not converted. 
	 * <code>(yyy) e</code> is converted in <code>j_xxx2yyy</code> when yyy is a
	 * builtin type.
	 * <code>(yyy) e</code> is converted in <code>e</code> otherwise.
	 * <code>e instanceof t</code> is converted into 
	 * <code>typeof(e) <: \type(t)</code>
	 **/
	FormulaWithSpecMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException {
		Formula res;
		FormulaWithSpecMethodDecl c = exp.exprToContextForm(config, methods, false);
		switch (getNodeType()) {
			case CAST :
				if (type.isBuiltin())
					res = cast(type, exp.getStateType(), c.getFormula());
				else
					res = c.getFormula();
				break;
			case LITERAL_instanceof :
				res =
					new UnaryForm(
						B_BOOL,
						new BinaryForm(
							Jm_IS_SUBTYPE,
							new BinaryForm(
								IFormToken.B_APPLICATION,
								TerminalForm.$typeof,
								c.getFormula()),
							new TTypeForm(IFormToken.Jm_T_TYPE, type)));
				break;
			default :
				return null;
		}
		return new FormulaWithSpecMethodDecl(c, res);
	}

	public String toJava(int indent) {
		switch (getNodeType()) {
			case CAST :
				return "(" + type.toJava() + ") (" + exp.toJava(indent) + ")";
			case LITERAL_instanceof :
				return exp.toJava(indent) + " instanceof " + type.toJava();
			case NEWARRAY :
				if (dim == null)
					return "new " + type.toJava() + exp.toJava(indent);
				else
					return "new " + type.toJava() + dim.toJava(indent);
			case LITERAL_new :
				return "new "
					+ type.toJava()
					+ "("
					+ (exp != null ? exp.toJava(indent) : "")
					+ ")";
			default :
				return "";
		}
	}

	public AST parse(AST tree) throws Jml2bException {
		//@ set parsed = true;
		AST subtree;
		setNodeType(tree.getType());
		setNodeText(tree.getText());
		switch (getNodeType()) {
			case CAST :
				type = new Type(getJmlFile(), tree.getFirstChild());
				subtree = type.parse(tree.getFirstChild());
				exp = Expression.createE(getJmlFile(), subtree);
				exp.parse(subtree);
				break;
			case LITERAL_instanceof :
				exp = Expression.createE(getJmlFile(), tree.getFirstChild());
				subtree = exp.parse(tree.getFirstChild());
				type =
					new Type(
						getJmlFile(),
						tree.getFirstChild().getNextSibling());
				type.parse(tree.getFirstChild().getNextSibling());
				break;
			case LITERAL_new :
				type = new Type(getJmlFile(), tree.getFirstChild());
				subtree = type.parse(tree.getFirstChild());
				if (subtree != null) {
					if (subtree.getType() == DIM_EXPRS) {
						setNodeType(NEWARRAY);
						dim =
							new DimExpr(getJmlFile(), subtree.getFirstChild());
						if (subtree.getNextSibling() != null) {
							type =
								Type.addDims(
									getJmlFile(),
									subtree.getNextSibling(),
									type);
						}
					} else if (subtree.getType() == LCURLY) {
						setNodeType(NEWARRAY);
						exp = Expression.createE(getJmlFile(), subtree);
						subtree = exp.parse(subtree);
					} else {
						exp = Expression.createE(getJmlFile(), subtree);
						subtree = exp.parse(subtree);
					}
				}
				break;
			default :
				throw new Jml2bException("");
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		switch (getNodeType()) {
			case LITERAL_new :
				{
					Vector parameters = new Vector();
					// link the type
					type.link(config, f);

					setStateType(type);

					if (exp != null) {
						// link parameters
						exp.linkParameters(config, f, parameters);
					}

					AClass c = type.getRefType();

					if (c == null) {
						throw new LinkException(
							"Found constructor for " + "non-reference type",
							this);
					}

					AMethod ctor = c.getConstructor(config, parameters);

					if (ctor == null) {
						throw new LinkException(
							"Cannot find constructor for "
								+ "class "
								+ c.getName()
								+ " with paramaters "
								+ Type.signatureToString(parameters.elements()),
							this);
					}

					ident = new Identifier(ctor);

					break;
				}
			case NEWARRAY :
				{
					// link the type
					type.link(config, f);

					if (dim == null) {
						setStateType(type);
						exp.linkStatement(config, f);
					} else {
						Type tmp = type;
						// add dimensions corresponding to the DIM_EXPRS statements
						DimExpr current = dim;
						while (current != null) {
							// add an array dimension
							tmp = new Type(config, tmp);
							// go to the next DIM_EXPRS statement
							current = current.getNext();
						}
						setStateType(tmp);
						// link the DIM_EXPRS statements
						dim.linkStatement(config, f);
					}
					break;
				}
			case LITERAL_instanceof :
				type.link(config, f);
				setStateType(Type.getBoolean());
				exp.linkStatement(config, f);
				// return a boolean type
				break;

				// same as instanceof, but return the type instead of a 
				// boolean
			case CAST :
				type.link(config, f);
				setStateType(type);

				exp.linkStatement(config, f);
				// return the type corresponding to the cast
				break;
		}
		return new LinkInfo(getStateType());
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		switch (getNodeType()) {
			case LITERAL_new :
			case NEWARRAY :
				return null;
			case LITERAL_instanceof :
				{
					Type t = exp.typeCheck(config, f);
					if (t.isRef())
						return Type.getBoolean();
					else
						throw new TypeCheckException(
							"Incompatible conditional operand types "
								+ t.toJava()
								+ " and ?"
								+ type.toJava(),
							this);
				}
			case CAST :
				Type t = exp.typeCheck(config, f);
				if (t.isRef() && type.isRef())
					return type; //TODO Completer les test du cast
				if (t.isNumeric() && type.isNumeric())
					return type;
				if (t.isBoolean() && type.isBoolean())
					return type;
				if (t.getTag() == Type.T_TYPE && type.getTag() == Type.T_TYPE)
					return type;
				throw new TypeCheckException(
					"Cannot cast from " + t.toJava() + " to ?" + type.toJava(),
					this);
		}
		return null;
	}

	public void processIdent() {
		if (exp != null)
			exp.processIdent();
		if (dim != null)
			dim.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException {
		if (exp != null)
			exp.isModifiersCompatible(config, modifiers);
		//        if (dim != null)
		//            dim.isModifiersCompatible(modifiers);
	}

	public JmlExpression instancie() {
		if (exp != null)
			exp = (Expression) exp.instancie();
		if (dim != null)
			dim = dim.instancie();
		return this;
	}

	public Expression subField(Field f, Field newF) {
		exp = (exp == null ? null : exp.subField(f, newF));
		return this;
	}

	public Expression subResult(String ww) {
		exp = (exp == null ? null : exp.subResult(ww));
		return this;
	}

	public Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) type);
		if (exp != null)
			res.addAll(exp.getParsedItems());
		if (dim != null)
			res.addAll(dim.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		type.setParsedItem(pi);
		if (exp != null)
			exp.setParsedItem(pi);
		if (dim != null)
			dim.setParsedItem(pi);
		change(pi);
	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public void old() {
		if (exp != null)
			exp.old();
	}

	public JmlExpression instancie(Expression b) {
		exp = (exp == null ? null : (Expression) exp.instancie(b));
		return this;
	}

	public boolean isConstant() {
		switch (getNodeType()) {
			case CAST :
				switch (type.getTag()) {
					case Type.T_INT :
					case Type.T_SHORT :
					case Type.T_CHAR :
					case Type.T_BYTE :
						return exp.isConstant();
				}
			default :
				return false;
		}
	}

	public int getValue() {
		switch (getNodeType()) {
			case CAST :
				switch (type.getTag()) {
					case Type.T_INT :
						return exp.getValue();
					case Type.T_SHORT :
						return (short) exp.getValue();
					case Type.T_CHAR :
						return (char) exp.getValue();
					case Type.T_BYTE :
						return (byte) exp.getValue();
				}
			default :
				throw new jml2b.exceptions.InternalError(
					"WithTypeExp.getValue() called for non-constant expression");
		}
	}

	/**
	 * Return the normal behaviour proof where the <code>arraylength</code>, 
	 * <code>xxxelements</code>, <code>instances</code> and <code>typeof</code>
	 * functions have been modified to take into account the creation of
	 * new arrays.
	 * @param name The set of array object names that are created
	 * @param nameType The type of the create array objects
	 * @param array_length The set of length fresh variable that have to be
	 * used to store the length of each created array.
	 * @param normalBehaviour The inital proof
	 **/
	/*@
	  @ requires parsed;
	  @*/
	private Proofs newArray(
		IJml2bConfiguration config,
		Formula name,
		Type nameType,
		Enumeration array_length,
		Proofs normalBehaviour)
		throws Jml2bException {

		if (array_length.hasMoreElements()) {
			String length = (String) array_length.nextElement();
			Formula newArraylength =
				new BinaryForm(
					B_OVERRIDING,
					TerminalForm.getArraylength(config),
					new BinaryForm(
						CONSTANT_FUNCTION,
						name,
						new TerminalForm(length)));
			// newArraylength = arraylength  <+ name * {length}

			Type elemtype = nameType.getElemType();
			if (elemtype.isArray()) {
				String f = freshRefelements();

				Formula newRefelements =
					new BinaryForm(
						B_OVERRIDING,
						ElementsForm.refelements,
						new TerminalForm(f));
				// newRefelements = refelements <+ f

				Formula ftype =
					new UnaryForm(IS_ARRAY, BinaryForm.getDefaultRefDecl());
				// ftype = name 
				//         >-> (0..length-1 
				//              >-> REFERENCES - (instances \/ {null})

				Proofs t1 =
					newArray(
						config,
						new TerminalForm("flatran(" + f + ")"),
						elemtype,
						array_length,
						normalBehaviour);
				Proofs t2 =
					t1.sub(new SubArrayElement("refelements", newRefelements));
				Proofs t3 = t2.sub(new SubArrayLength(newArraylength));

				Proofs t4;
				if (name.getNodeType() == IFormToken.B_ACCOLADE) {
					t4 =
						t3.sub(
							new SubTypeofSingle(
								((UnaryForm) name).getExp(),
								new TTypeForm(IFormToken.Jm_T_TYPE, nameType)));
					t4 =
						t4.sub(
							new SubInstancesSingle(
								((UnaryForm) name).getExp()));
				} else {
					t4 =
						t3.sub(
							new SubTypeofSet(
								name,
								new TTypeForm(IFormToken.Jm_T_TYPE, nameType)));
					t4 = t4.sub(new SubInstancesSet(name));
				}
				return t4.quantify(f, ftype);
			} else {
				String elements = null;
				elements =
					ElementsForm
						.getElementsName(elemtype)
						.getNonAmbiguousName();
				Formula newElements =
					new BinaryForm(
						B_OVERRIDING,
						ElementsForm.getElementsName(elemtype),
						new TriaryForm(
							CONSTANT_FUNCTION_FUNCTION,
							name,
							new BinaryForm(
								B_INTERVAL,
								new TerminalForm(0),
								new BinaryForm(
									Ja_NEGATIVE_OP,
									new TerminalForm(length),
									new TerminalForm(1))),
							getDefaultArrayInitialiser(elemtype)));
				// newElements = elements <+ name * {0..length-1 * {default}}

				Proofs t2 =
					normalBehaviour.sub(
						new SubArrayElement(elements, newElements));
				Proofs t3 = t2.sub(new SubArrayLength(newArraylength));
				Proofs t4;
				if (name.getNodeType() == IFormToken.B_ACCOLADE) {
					t4 =
						t3.sub(
							new SubTypeofSingle(
								((UnaryForm) name).getExp(),
								new TTypeForm(IFormToken.Jm_T_TYPE, nameType)));
					t4 =
						t4.sub(
							new SubInstancesSingle(
								((UnaryForm) name).getExp()));
				} else {
					t4 =
						t3.sub(
							new SubTypeofSet(
								name,
								new TTypeForm(IFormToken.Jm_T_TYPE, nameType)));
					t4 = t4.sub(new SubInstancesSet(name));
				}
				return t4;
			}
		} else {
			Proofs t4;
			if (name.getNodeType() == IFormToken.B_ACCOLADE) {
				t4 =
					normalBehaviour.sub(
						new SubTypeofSingle(
							((UnaryForm) name).getExp(),
							new TTypeForm(IFormToken.Jm_T_TYPE, nameType)));
				t4 =
					t4.sub(new SubInstancesSingle(((UnaryForm) name).getExp()));
			} else {
				t4 =
					normalBehaviour.sub(
						new SubTypeofSet(
							name,
							new TTypeForm(IFormToken.Jm_T_TYPE, nameType)));
				t4 = t4.sub(new SubInstancesSet(name));
			}
			return t4;
		}
	}

	public Proofs wp(
		IJml2bConfiguration config,
		String result,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		String oo;
		Proofs p;
		switch (getNodeType()) {
			case LITERAL_new :
				// oo is the new object.
				oo = freshObject();

				// e = oo.ident(exp)
				MethodCallExp e =
					new MethodCallExp(
						MyToken.METHOD_CALL,
						new BinaryExp(
							DOT,
							new TerminalExp(oo, type),
							".",
							new TerminalExp(ident)),
						"()",
						exp);

				// x = [resultingVar := oo][typeof := typeof <+ {oo |-> type]nB                    
				p =
					((Proofs) normalBehaviour.clone())
						.sub(new SubTmpVar(result, new TerminalForm(oo)))
						.sub(
							new SubTypeofSingle(
								new TerminalForm(oo),
								new TTypeForm(IFormToken.Jm_T_TYPE, type)));

				// !oo.(oo :  REFERENCES - (instances \/ null)
				//      => [oo.ident(exp)](fresh(), 
				//                         [instances := instances \/ {oo}]x,
				//                         eB)
				p =
					e.wp(
						config,
						fresh(),
						p.sub(new SubInstancesSingle(new TerminalForm(oo))),
						exceptionalBehaviour);
				p.addHyp(BinaryForm.getDefaultRefDecl(new TerminalForm(oo)));

				Enumeration en =
					ident.mth.getDefiningClass().getOwnFields().elements();
				while (en.hasMoreElements()) {
					AField element = (AField) en.nextElement();
					if (element.getModifiers().isStatic())
						continue;
					element.nameIndex = IdentifierResolver.addIdent(element);
					ModifiedFieldForm mff =
						new ModifiedFieldForm(element, ident.mth);
					p =
						p.sub(
							new SubForm(
								new TerminalForm(new Identifier(element)),
								mff));
					p.addHyp(
						new TriaryForm(
							NEW_OBJECT,
							new TerminalForm(oo),
							new TerminalForm(new Identifier(element)),
							mff),
						new ColoredInfo(type),
						VirtualFormula.LOCALES);
					//					if (element.getType().isBuiltin())
					//						p =
					//							p.quantify(
					//								mff.getNodeText(),
					//								new BinaryForm(
					//									B_PARTIALFUNCTION,
					//									TerminalForm.REFERENCES,
					//									new TTypeForm(
					//										IFormToken.T_TYPE,
					//										element.getType())));
					//					else 
					if (element.getType().isArray()) {
						jml2b.formula.ElementsForm elements =
							ElementsForm.getElementsName(element.getType());
						p =
							p.quantify(
								mff.getNodeText(),
								elements.getType(),
								new ColoredInfo());

					} else {
						p =
							p.quantify(
								mff,
								new BinaryForm(
									IS_MEMBER_FIELD,
									new TTypeForm(
										IFormToken.T_TYPE,
										new Type(element.getDefiningClass())),
									new TTypeForm(
										IFormToken.T_TYPE,
										element.getType())));
					}
				}
				return p.quantify(
					oo,
					TerminalForm.$References,
					new ColoredInfo(type, ColoredInfo.NEW, oo));
			case NEWARRAY :
				oo = freshObject();

				//set of fresh variables which will be used to store the
				//evaluation of the lengths of each dimension.                    
				Vector dimExpr = new Vector();
				DimExpr de = dim;
				while (de != null) {
					dimExpr.add(fresh());
					de = de.getNext();
				}

				Formula u = new UnaryForm(B_ACCOLADE, new TerminalForm(oo));

				p =
					((Proofs) normalBehaviour.clone()).sub(
						new SubTmpVar(result, new TerminalForm(oo)));

				Proofs v =
					newArray(config, u, getStateType(), dimExpr.elements(), p);

				v.addHyp(BinaryForm.getDefaultRefDecl(new TerminalForm(oo)));

				return dim.newArrayLength(
					config,
					dimExpr,
					v.quantify(
						new TerminalForm(oo),
						TerminalForm.$References,
						new ColoredInfo(type, ColoredInfo.NEW, oo)),
					exceptionalBehaviour);

			case CAST :
				if (type.isBuiltin())
					return exp.wp(
						config,
						result,
						cast(
							type,
							exp.getStateType(),
							result,
							((Proofs) normalBehaviour.clone())).addBox(
							new ColoredInfo(type)),
						exceptionalBehaviour);
				else {
					// s = resultingVar == null 
					//     || \typeof(resultingVar) <: type
					Formula s =
						new BinaryForm(
							Ja_OR_OP,
							new BinaryForm(
								Ja_EQUALS_OP,
								new TerminalForm(result),
								new TerminalForm(Ja_LITERAL_null, "null")),
							new BinaryForm(
								Jm_IS_SUBTYPE,
								new BinaryForm(
									IFormToken.B_APPLICATION,
									TerminalForm.$typeof,
									new TerminalForm(result)),
								new TTypeForm(IFormToken.Jm_T_TYPE, type)));
					Proofs lv =
						exceptionalBehaviour.throwException(
							config,
							classCastException);
					lv.addHyp(
						Formula.not(s),
						new ColoredInfo(exp, ColoredInfo.IS_NOT_CASTABLE),
						VirtualFormula.LOCALES);
					Proofs tmp = (Proofs) normalBehaviour.clone();
					tmp.addHyp(
						s,
						new ColoredInfo(type),
						VirtualFormula.LOCALES);
					lv.addAll(tmp);
					return exp.wp(config, result, lv, exceptionalBehaviour);
				}
			case LITERAL_instanceof :
				String vv = fresh();

				// s = bool(vv /= null && typeof(vv) <: type)
				Formula s =
					new UnaryForm(
						B_BOOL,
						Formula.and(
							new BinaryForm(
								Ja_DIFFERENT_OP,
								new TerminalForm(vv),
								new TerminalForm(Ja_LITERAL_null, "null")),
							new BinaryForm(
								Jm_IS_SUBTYPE,
								new BinaryForm(
									IFormToken.B_APPLICATION,
									TerminalForm.$typeof,
									new TerminalForm(vv)),
								new TTypeForm(IFormToken.Jm_T_TYPE, type))));
				return exp.wp(
					config,
					vv,
					((Proofs) normalBehaviour.clone()).sub(
						new SubTmpVar(result, s)),
					exceptionalBehaviour);
			default :
				throw new jml2b.exceptions.InternalError(
					"WithTypeExp.wp: bad node type: " + getNodeType());
		}
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		if (exp != null)
			exp.getPrecondition(config, modifies, req, ens);
		if (dim != null) {
			DimExpr le = dim;
			while (le != null) {
				le.getExp().getPrecondition(config, modifies, req, ens);
				le = le.getNext();
			}
		}
	}

	public void collectCalledMethod(Vector calledMethod) {
		if (exp != null)
			exp.collectCalledMethod(calledMethod);
		if (dim != null) {
			DimExpr le = dim;
			while (le != null) {
				le.getExp().collectCalledMethod(calledMethod);
				le = le.getNext();
			}
		}
	}
	static final long serialVersionUID = -7901462666342789890L;

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#getFreeVariable(java.util.Set)
	 */
	void getFreeVariable(Set s) {
		if (exp != null)
			exp.getFreeVariable(s);
		if (dim != null) {
			DimExpr le = dim;
			while (le != null) {
				le.getExp().getFreeVariable(s);
				le = le.getNext();
			}
		}
	}

	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

	/**
	 * @return
	 */
	public Type getType() {
		return type;
	}

}