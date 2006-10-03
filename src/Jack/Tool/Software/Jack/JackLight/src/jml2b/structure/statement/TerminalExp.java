//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TerminalExp
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import jack.util.Logger;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AMethod;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a terminal expression.
 * <p>
 * Java terminal expressions can be:
 * <UL>
 * <li> an identifier
 * <li> a Java builtin type
 * <li> a float literal
 * <li> a char literal
 * <li> a integer literal
 * <li> a string literal
 * <li> <code>false</code>
 * <li> <code>true</code>
 * <li> <code>null</code>
 * <li> <code>this</code>
 * <li> <code>super</code>
 * </UL>
 * Jml terminal expressions can be:
 * <UL>
 * <li> <code>\result</code>
 * </UL>
 * @author L. Burdy, A. Requet
 **/
public class TerminalExp extends Expression {

	/**
	 * Converts an hexadecimal number into an integer
	 * @param s The string to convert
	 * @return the string corresponding to the calculated integer
	 **/
	private static String hexa2Int(String s) {
		int j = 0;
		for (int i = 2; i < s.length(); i++)
			j
				+= (int) (s.charAt(i) <= '9'
					? s.charAt(i) - '0'
					: (s.charAt(i) <= 'F'
						? s.charAt(i) - 'A' + 10
						: s.charAt(i) - 'a' + 10))
				<< ((s.length() - 1 - i) * 4);
		return j + "";
	}

	/**
	 * Converts an octal number into an integer
	 * @param s The string to convert
	 * @return the string corresponding to the calculated integer
	 **/
	private static String octal2Int(String s) {
		int j = 0;
		for (int i = 1; i < s.length(); i++)
			j += (int) (s.charAt(i) - '0') << ((s.length() - 1 - i) * 3);
		return j + "";
	}

	/**
	 * The identifier corresponding to this expression. It can be 
	 * <code>null</code> if the expression is a constant.
	 **/
	private Identifier ident;

	/**
	 * End of an expression created from an identifier and a string. This is 
	 * used to create expression like c_my_class_an_instance. The part 
	 * c_my_class comes from an class identifier and _an_instance is the 
	 * postfix part.
	 **/
	private boolean subident = false;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	TerminalExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an expression that is not a Java identifer.
	 * @param nodeType The node type of this expression
	 * @param nodeText The string corresponding to this expression
	 **/
	public TerminalExp(int nodeType, String nodeText) {
		super(nodeType, nodeText);
	}

	/**
	 * Constructs an expression that is an identifier but not a Java identifer.
	 * @param nodeText The string corresponding to this expression
	 **/
	public TerminalExp(String nodeText, Type t) {
		super(IDENT, nodeText);
		setStateType(t);
	}

	/**
	 * Constructs an expression from a Java identifer and a postfix string.
	 * @param ident The identifier corresponding to this expression
	 * @param subident The postfix string associated with this expression
	 **/
	public TerminalExp(Identifier ident, String subident) {
		super(IDENT, "");
		this.ident = ident;
		this.subident = true;
	}

	/**
	 * Constructs an expression from a Java identifer.
	 * @param ident The identifier corresponding to this expression
	 **/
	public TerminalExp(Identifier ident) {
		super(IDENT, "");
		this.ident = ident;
	}

	public Object clone() {
		return this;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& (getNodeText() == null
				? e.getNodeText() == null
				: (e.getNodeText() != null
					&& getNodeText().equals(e.getNodeText())))
			&& subident == ((TerminalExp) e).subident
			&& (ident == null
				? ((TerminalExp) e).ident == null
				: (((TerminalExp) e).ident != null
					&& ident.equals(((TerminalExp) e).ident)));
	}

	FormulaWithPureMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws PogException {
		byte n = -1;
		switch (getNodeType()) {
			case IDENT :
				n = Ja_IDENT;
				break;
			case CHAR_LITERAL :
				n = Ja_CHAR_LITERAL;
				break;
			case NUM_INT :
				n = Ja_NUM_INT;
				break;
			case LITERAL_false :
				n = Ja_LITERAL_false;
				break;
			case LITERAL_true :
				n = Ja_LITERAL_true;
				break;
			case JAVA_BUILTIN_TYPE :
				n = Ja_JAVA_BUILTIN_TYPE;
				break;
			case LITERAL_null :
				n = Ja_LITERAL_null;
				break;
			case LITERAL_this :
				n = Ja_LITERAL_this;
				break;
			case LITERAL_super :
				n = Ja_LITERAL_super;
				break;
			case STRING_LITERAL :
				n = Ja_STRING_LITERAL;
				break;
			case T_RESULT :
				n = Jm_T_RESULT;
				break;
			case BTRUE :
				n = B_BTRUE;
				pred = false;
				break;
			case NUM_FLOAT :
				throw new PogException(
					"Sorry, this version does not treat float.",
					this);
			default :
				Logger.err.println("TerminalExp.exprToForm() " + getNodeType());
				break;
		}
		if (pred) {
			BinaryForm res =
				new BinaryForm(
					Ja_EQUALS_OP,
					new TerminalForm(n, getNodeText(), ident, subident),
					new TerminalForm(IFormToken.Ja_LITERAL_true));
			return new FormulaWithPureMethodDecl(res);
		} else {
			TerminalForm res =
				new TerminalForm(n, getNodeText(), ident, subident);
			res.setBox((ParsedItem) this);
			return new FormulaWithPureMethodDecl(res);
		}
	}

	public String toJava(int indent) {
		switch (getNodeType()) {
			case LITERAL_true :
				return "true";
			case LITERAL_false :
				return "false";
			case MyToken.BTRUE :
				return "true";
			case IDENT :
				if (ident != null) {
					if (ident.idType == Identifier.ID_FIELD
						&& ident.field.getModifiers() != null
						&& ident.field.getModifiers().isStatic())
						return ident.field.getDefiningClass().getName()
							+ "."
							+ ident.getName();
					else
						return ident.getName();
				}
			default :
				return getNodeText();
		}
	}

	public AST parse(AST tree) {
		//@ set parsed = true;
		switch (tree.getType()) {
			case IDENT :
				setNodeType(tree.getType());
				setNodeText(""); // A v?rifier tree.getText();
				ident = new Identifier(tree.getText());
				break;
			case CHAR_LITERAL :
				setNodeType(tree.getType());
				if (tree.getText().length() >= 3
					&& tree.getText().charAt(1) == '\\')
					switch (tree.getText().charAt(2)) {
						case 'u' :
							// unicode value
							setNodeText(
								hexa2Int(
									tree.getText().substring(
										1,
										tree.getText().length() - 1)));
							break;
						case 'b' :
							setNodeText("8");
							break;
						case 't' :
							setNodeText("9");
							break;
						case 'n' :
							setNodeText("10");
							break;
						case 'f' :
							setNodeText("12");
							break;
						case 'r' :
							setNodeText("13");
							break;
						case '"' :
							setNodeText("34");
							break;
						case '\'' :
							setNodeText("39");
							break;
						case '\\' :
							setNodeText("92");
							break;
						default :
							// OctalEscape.
							setNodeText(tree.getText());
					} else
					setNodeText(((int) tree.getText().charAt(1)) + "");
				break;
			case NUM_INT :
				setNodeType(tree.getType());
				// hexadecimal value
				if (tree.getText().length() >= 2
					&& (tree.getText().charAt(1) == 'x'
						|| tree.getText().charAt(1) == 'X'))
					setNodeText(hexa2Int(tree.getText()));
				// octal value
				else if (
					tree.getText().length() >= 2
						&& tree.getText().charAt(0) == '0')
					setNodeText(octal2Int(tree.getText()));
				// long value
				else if (
					tree.getText().charAt(tree.getText().length() - 1) == 'l'
						|| tree.getText().charAt(tree.getText().length() - 1)
							== 'L')
					setNodeText(
						tree.getText().substring(
							0,
							tree.getText().length() - 2));
				else
					setNodeText(tree.getText());
				break;
			case LITERAL_false :
				setNodeType(tree.getType());
				setNodeText("false");
				break;
			case LITERAL_true :
				setNodeType(tree.getType());
				setNodeText("true");
				break;
			case JAVA_BUILTIN_TYPE :
			case LITERAL_null :
			case LITERAL_this :
			case LITERAL_super :
			case STRING_LITERAL :
			case T_RESULT :
			case NUM_FLOAT :
				setNodeType(tree.getType());
				setNodeText(tree.getText());
				break;
		}
		return tree.getNextSibling();
	}

	/**
	 * Links a constructor call.
	 * @param config the current configuration of the generator
	 * @param cl The class where the constructor is searched
	 * @param parameters set of types of the method parameters
	 * @return the resulting link informations
	 * @throws Jml2bException
	 **/
	void linkConstructorCall(
		IJml2bConfiguration config,
		AClass cl,
		Vector parameters)
		throws Jml2bException {
		if (cl == null) {
			throw new LinkException(
				"Attempt to call constructor for " + "null class",
				this);
		}

		AMethod ctor = cl.getConstructor(config, parameters);

		if (ctor == null) {
			throw new LinkException("Unable to find super constructor ", this);
		}
		ident = new Identifier(ctor);
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		switch (getNodeType()) {
			case CHAR_LITERAL :
				setStateType(Type.getChar());
				return new LinkInfo(getStateType());

			case IDENT :
				LinkInfo res = ident.linkFieldIdent(config, f, this);
				if (ident.idType == Identifier.ID_CLASS)
					setStateType(new Type(Type.T_CLASS));
				else
					setStateType(res.getType());
				return res;

			case LITERAL_null :
				setStateType(new Type(Type.T_NULL));
				return new LinkInfo(getStateType());

			case NUM_INT :
				setStateType(Type.getInteger());
				return new LinkInfo(getStateType());

			case STRING_LITERAL :
				setStateType(
					new Type(
						((JavaLoader) config.getPackage()).getJavaLang().getAndLoadClass(
							config,
							"String")));
				return new LinkInfo(getStateType());

			case BTRUE :
			case LITERAL_true :
			case LITERAL_false :
				setStateType(new Type(Type.T_BOOLEAN));
				return new LinkInfo(getStateType());

			case T_RESULT :
				if (f.isResultAdmitted()) {
					setStateType(f.currentMethod.getReturnType());
					ident =
						new Identifier(
							new Field(
								this,
								null,
								f.currentMethod.getReturnType(),
								getNodeText(),
								null));
					return new LinkInfo(getStateType());
				} else
					throw new LinkException(
						"\\result can only occur in an ensures clause.",
						this);
			case LITERAL_super :
				// set the type of the node to the superclass of the current 
				// class
				setStateType(f.getCurrentClass().getSuper());
				// replace super by this
				setNodeType(LITERAL_this);
				setNodeText("this");
				return new LinkInfo(getStateType());

			case LITERAL_this :
				setStateType(new Type(f.currentClass));
				return new LinkInfo(getStateType());

		}
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return getStateType();
	}

	/**
	 * When this terminal expression is an identifier, a name index is assigned 
	 * and its name is stored in the identifier array.
	 **/
	public void processIdent() {
		if (ident != null)
			switch (ident.idType) {
				case Identifier.ID_CLASS :
					ident.cl.nameIndex = IdentifierResolver.addIdent(ident.cl);
					break;
				case Identifier.ID_PACKAGE :
					ident.pkg.nameIndex =
						IdentifierResolver.addIdent(ident.pkg);
					break;
				case Identifier.ID_METHOD :
					//ident.mth.nameIndex = Pog.addIdent(ident.mth);
					break;
				case Identifier.ID_FIELD :
					ident.field.nameIndex =
						IdentifierResolver.addIdent(ident.field);
					break;
			}
	}

	/**
	 * If the expression is an identifier, test if their modifiers are
	 *  compatible with the invariant modifiers.
	 **/
	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException {
		boolean compatible = true;
		if (ident != null)
			switch (ident.idType) {
				case Identifier.ID_CLASS :
					break;
				case Identifier.ID_PACKAGE :
					break;
				case Identifier.ID_METHOD :
					compatible =
						((Modifiers) ident.mth.getModifiers()).isCompatible(modifiers);
					break;
				case Identifier.ID_FIELD :
					try {
						compatible =
							ident.field.getModifiers() == null
								|| ident.field
									== (Field) config.getArray().fields.get(0)
								|| ((Modifiers) ident.field.getModifiers()).isCompatible(
									modifiers);
					} catch (Jml2bException je) {
						throw new LinkException(je.getMessage(), this);
					}
					break;
			}
		if (!compatible)
			throw new LinkException("Incompatibility in invariant", this);
	}

	/**
	 * Returns a dot expression <code>this.e</code> where <code>e</code> is the
	 * current expression when it is an identifer that corresponds to a non
	 * static field or non static method.
	 **/
	public JmlExpression instancie() {
		BinaryExp b;
		if (ident != null)
			switch (ident.idType) {
				case Identifier.ID_FIELD :
					if (ident.field.isLocal()
						|| ident.field.getModifiers().isStatic())
						break;
					b =
						new BinaryExp(
							DOT,
							new TerminalExp(LITERAL_this, "this"),
							".",
							this);
					b.setStateType(getStateType());
					b.setParsedItem(this);
					return b;
				case Identifier.ID_METHOD :
					if (ident.mth.getModifiers().isStatic())
						break;
					b =
						new BinaryExp(
							DOT,
							new TerminalExp(LITERAL_this, "this"),
							".",
							this);
					b.setStateType(getStateType());
					return b;
				default :
					break;
			}
		return this;
	}

	public Expression subField(Field f, Field newF) {
		if (ident != null)
			switch (ident.idType) {
				case Identifier.ID_FIELD :
					if (ident.field == f) {
						TerminalExp res = new TerminalExp(new Identifier(newF));
						res.setStateType(getStateType());
						return res;
					}
				default :
					return this;
			} else
			return this;
	}

	public Expression subResult(String ww) {
		if (getNodeType() == T_RESULT) {
			TerminalExp res = new TerminalExp(IDENT, ww);
			res.setStateType(getStateType());
			return res;
		}
		else
			return this;
	}
	/**
	 * If the current expression is <code>LITERAL_this</code>, 
	 * return <code>b</code> else return <code>this</code>.
	 **/
	public JmlExpression instancie(Expression b) {
		switch (getNodeType()) {
			case LITERAL_this :
				return b;
			default :
				return this;
		}
	}

	public Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	public boolean isConstant() {
		switch (getNodeType()) {
			case CHAR_LITERAL :
			case NUM_INT :
			case BTRUE :
			case LITERAL_true :
			case LITERAL_false :
				return true;
			case LITERAL_null :
			case STRING_LITERAL :
			default :
				return false;
		}
	}

	public int getValue() {
		switch (getNodeType()) {
			case CHAR_LITERAL :
				return (int) getNodeText().charAt(0);
			case NUM_INT :
				return Integer.parseInt(getNodeText());
			case BTRUE :
			case LITERAL_true :
				return 1;
			case LITERAL_false :
				return 0;
			case LITERAL_null :
			case STRING_LITERAL :
			default :
				throw new InternalError(
					"Expression.getValue() called for "
						+ "non-constant expression");
		}

	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public void old() {
	}

	/**
	 * Returns the identifier.
	 * @return <code>ident</code>
	 */
	public Identifier getIdent() {
		return ident;
	}

	static final long serialVersionUID = -8295372047797723108L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens) {
	}

	public void collectCalledMethod(Vector calledMethod) {
	}

	void getFreeVariable(Set s) {
		if (ident != null && ident.idType == Identifier.ID_FIELD)
			s.add(ident.field);
	}

}