//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: TerminalForm.java
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/
package jml2b.formula;

import java.util.Set;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;

/**
 * This class implements terminal formula: identifiers, literal constants and
 * builtin types. The node type can be
 * <UL>
 * <li>Ja_IDENT
 * <li>FINAL_IDENT
 * <li>B_BTRUE
 * <li>Ja_CHAR_LITERAL
 * <li>Ja_NUM_INT
 * <li>Ja_LITERAL_false
 * <li>Ja_LITERAL_true
 * <li>Ja_JAVA_BUILTIN_TYPEs
 * <li>Ja_LITERAL_null
 * <li>Ja_LITERAL_this
 * <li>Ja_LITERAL_super
 * <li>Ja_STRING_LITERAL
 * <li>Jm_T_RESULT
 * </UL>
 * 
 * @author L.Burdy
 */
public class TerminalForm extends Formula {

	/**
	 * The formula <code>instances</code>. In the B lemmas,
	 * <code>instances</code> is the set of all current class instances.
	 */
	public final static TerminalForm instances = new TerminalForm("instances");

	/**
	 * The formula <code>typeof</code>. In the B lemmas, <code>typeof</code>
	 * is a function that assign a type to an instance.
	 */
	public final static TerminalForm typeof = new TerminalForm("typeof");

	/**
	 * The formula <code>arraylength</code>. In the B lemmas,
	 * <code>arraylength</code> is a function that assign the length to an
	 * array instance.
	 */
	public static TerminalForm arraylength;

	public static TerminalForm getArraylength(IJml2bConfiguration config) throws Jml2bException {
		if (arraylength == null)
			return arraylength = new TerminalForm(new Identifier((Field) config.getArray().fields.get(0)));
		else
			return arraylength;
	}

	/**
	 * The constant formula <code>REFERENCES</code>. In the B lemmas,
	 * <code>REFERENCES</code> is the set of all existing or potential
	 * instances.
	 */
	public final static TerminalForm REFERENCES = new TerminalForm(FINAL_IDENT, "REFERENCES");

	/**
	 * The constant formula <code>elemtype</code>, In the B lemmas,
	 * <code>elemtype</code> is a function that assign the type of its element
	 * to an array instance.
	 */
	public final static TerminalForm elemtype = new TerminalForm(FINAL_IDENT, "elemtype");

	/**
	 * The constant formula <code>j_int2short</code>, In the B lemmas,
	 * <code>j_int2short</code> is a function that converts an int into a
	 * short.
	 */
	public final static TerminalForm j_int2short = new TerminalForm(FINAL_IDENT, "j_int2short");

	/**
	 * The constant formula <code>j_int2byte</code>, In the B lemmas,
	 * <code>j_int2byte</code> is a function that converts an int into a byte.
	 */
	public final static TerminalForm j_int2byte = new TerminalForm(FINAL_IDENT, "j_int2byte");

	/**
	 * The constant formula <code>j_int2char</code>, In the B lemmas,
	 * <code>j_int2char</code> is a function that converts an int into a char.
	 */
	public final static TerminalForm j_int2char = new TerminalForm(FINAL_IDENT, "j_int2char");

	/**
	 * Parsed item corresponding to the terminal formula.
	 */
	private ParsedItem box;

	/**
	 * String corresponding to the formula. It can be empty if the formula
	 * corresponds to an identifier.
	 */
	protected String nodeText;

	/**
	 * Identifier corresponding to the formula. It can be null if the formula
	 * does not correspond to an identifier.
	 */
	protected Identifier ident;

	/**
	 * End of a formula create from an identifier and a string. This is used to
	 * create formula like c_my_class_an_instance. The part c_my_class comes
	 * from a class identifier and _an_instance is the postfix part.
	 */
	protected boolean postfix;

	protected TerminalForm(TerminalForm f) {
		super(f.getNodeType());
		nodeText = f.nodeText;
		ident = f.ident;
		postfix = f.postfix;
	}

	/**
	 * Constructs a terminal formula.
	 * 
	 * @param nodeType
	 *                    The node type of this formula
	 * @param nodeText
	 *                    The string corresponding to this formula
	 * @param ident
	 *                    The identifier corresponding to this formula
	 * @param subident
	 *                    The postfix string associated with this formula
	 */
	public TerminalForm(byte nodeType, String nodeText, Identifier ident, boolean subident) {
		super(nodeType);
		this.nodeText = nodeText;
		this.ident = ident;
		this.postfix = subident;
	}

	/**
	 * Constructs a formula that is not a Java identifer.
	 * 
	 * @param nodeType
	 *                    The node type of this formula
	 */
	public TerminalForm(byte nodeType) {
		this(nodeType, "", null, false);
	}

	/**
	 * Constructs a formula that is not a Java identifer.
	 * 
	 * @param nodeType
	 *                    The node type of this formula
	 * @param nodeText
	 *                    The string corresponding to this formula
	 */
	public TerminalForm(byte nodeType, String nodeText) {
		this(nodeType, nodeText, null, false);
	}

	/**
	 * Constructs a formula that is a <code>Ja_NUM_INT</code>.
	 * 
	 * @param v
	 *                    The integer value
	 */
	public TerminalForm(int v) {
		this(Ja_NUM_INT, "" + v, null, false);
	}

	/**
	 * Constructs a formula that is an identifier but not a Java identifer.
	 * 
	 * @param nodeText
	 *                    The string corresponding to this formula
	 */
	public TerminalForm(String nodeText) {
		this(Ja_IDENT, nodeText, null, false);
	}

	/**
	 * Constructs a formula from a Java identifer.
	 * 
	 * @param ident
	 *                    The identifier corresponding to this formula
	 */
	public TerminalForm(Identifier ident) {
		this(Ja_IDENT, "", ident, false);
	}

	/**
	 * Constructs a formula from a Java identifer and a postfix string.
	 * 
	 * @param ident
	 *                    The identifier corresponding to this formula
	 * @param subident
	 *                    The postfix string associated with this formula
	 */
	public TerminalForm(Identifier ident, String subident) {
		this(Ja_IDENT, "", ident, true);
	}

	public Object clone() {
		if (!(this instanceof ElementsForm) && getNodeType() == IFormToken.Ja_IDENT && this != instances
			&& this != typeof && this != arraylength) {
			TerminalForm res = new TerminalForm(getNodeType(), nodeText, ident, postfix);
			res.box = box;
			return res;
		} else
			return this;
	}

	public void processIdent() {
		if (ident != null)
			switch (ident.idType) {
				case Identifier.ID_CLASS :
					ident.cl.nameIndex = IdentifierResolver.addIdent(ident.cl);
					break;
				case Identifier.ID_PACKAGE :
					ident.pkg.nameIndex = IdentifierResolver.addIdent(ident.pkg);
					break;
				case Identifier.ID_METHOD :
					//ident.mth.nameIndex = Pog.addIdent(ident.mth);
					break;
				case Identifier.ID_FIELD :
					ident.field.nameIndex = IdentifierResolver.addIdent(ident.field);
					break;
			}
	}

	public Formula instancie(Formula b) {
		switch (getNodeType()) {
			case Ja_LITERAL_this :
				return b;
			default :
				return this;
		}
	}

	public void garbageIdent() {
		if (ident != null)
			switch (ident.idType) {
				case Identifier.ID_CLASS :
					break;
				case Identifier.ID_PACKAGE :
					break;
				case Identifier.ID_METHOD :
					break;
				case Identifier.ID_FIELD :
					ident.field.garbage = false;
					break;
			}
	}

	public void getFields(Set fields) {
		if (ident != null && ident.idType == Identifier.ID_FIELD
				&& !ident.field.isLocal()
			&& (ident.field.getModifiers() == null || !ident.field.getModifiers().isFinal()))
			fields.add(ident.field);
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		switch (getNodeType()) {
			case Ja_IDENT :
				if (a.getNodeType() == Ja_IDENT && equals(a)) {
					return (Formula) b.clone();
				} else
					return this;
			case Jm_T_RESULT :
				if (a.getNodeType() == Jm_T_RESULT)
					return (Formula) b.clone();
				else
					return this;
			case Ja_LITERAL_this :
				if (a.getNodeType() == Ja_LITERAL_this)
					return (Formula) b.clone();
				else
					return this;
			default :
				return this;
		}
	}

	public Formula subIdent(String a, Formula b) {
		switch (getNodeType()) {
			case Ja_IDENT :
				if (a.equals(getNonAmbiguousName()))
					return (Formula) b.clone();
			default :
				return this;
		}
	}

	public boolean equals(Object f) {
		return getNodeType() == ((Formula) f).getNodeType()
				&& (ident == null ? ((TerminalForm) f).ident == null : ident.equals(((TerminalForm) f).ident))
				&& postfix == ((TerminalForm) f).postfix
				&& (nodeText == null ? ((TerminalForm) f).nodeText == null : nodeText
						.equals(((TerminalForm) f).nodeText));
	}

	public boolean is(Formula f) {
		return getNodeType() == f.getNodeType() && ((TerminalForm) f).nodeText.equals(getNonAmbiguousName());
	}

	public int contains(Vector selectedFields) {
		return 0;
	}

	public boolean isObvious(boolean atTheEnd) {
		return getNodeType() == B_BTRUE;
	}

		public String getNonAmbiguousName() {
		switch (getNodeType()) {
			case Ja_IDENT :
				String res = "";
				if (getNodeText() != null)
					res = getNodeText();
				if (ident != null)
					switch (ident.idType) {
						case Identifier.ID_CLASS :
							res += ident.cl.getBName();
							break;
						case Identifier.ID_FIELD :
							if (ident.field.isExpanded())
								return Integer.toString(ident.field.getAssign().getValue());
							res += ident.field.getBName();
							break;
						case Identifier.ID_METHOD :
							res += ident.mth.getBName();
							break;
						default :
							throw new jml2b.exceptions.InternalError("TerminalForm.toB(): IDENT: " + ident.getName()
																		+ " with idType: " + ident.idType);
					}
				if (postfix)
					res += "an_instance";
				return res;
			default :
				return getNodeText();
		}

	}

	public Formula suppressSpecialOld(int token) {
		return this;
	}

	/**
	 * Returns the nodeText.
	 * 
	 * @return String
	 */
	public String getNodeText() {
		return nodeText;
	}

	/**
	 * Sets the box.
	 * 
	 * @param box
	 *                    The box to set
	 */
	public void setBox(ParsedItem box) {
		this.box = box;
	}

	static final long serialVersionUID = -5569956314641460620L;

	/*
	 * (non-Javadoc)
	 * 
	 * @see jml2b.formula.Formula#getBasicType()
	 */
	public BasicType getBasicType() {
		switch (getNodeType()) {
			case Ja_IDENT :
				BasicType type = null;
				if (getNodeText() != null) {
					if (getNodeText().equals("j_or") || getNodeText().equals("j_and") || getNodeText().equals("j_xor")
						|| getNodeText().equals("j_shl") || getNodeText().equals("j_shr")
						|| getNodeText().equals("j_ushr"))
						type = new BasicType(BasicType.ZType, new BasicType(BasicType.ZType, BasicType.ZType));
					else if (getNodeText().equals("typeof"))
						type = new BasicType(BasicType.RefType, BasicType.TypesType);
					else if (getNodeText().equals("instances"))
						type = new BasicType(BasicType.RefType, BasicType.PropType);
					else if (getNodeText().equals("arraylength"))
						type = new BasicType(BasicType.RefType, BasicType.ZType);
					else if (getNodeText().indexOf("refelements") == 0)
						type = new BasicType(BasicType.RefType, new BasicType(BasicType.ZType, BasicType.RefType));
					else if (getNodeText().indexOf("booleanelements") == 0)
						type = new BasicType(BasicType.RefType, new BasicType(BasicType.ZType, BasicType.BoolType));
					else if (getNodeText().indexOf("byteelements") == 0 || getNodeText().indexOf("charelements") == 0
								|| getNodeText().indexOf("intelements") == 0
								|| getNodeText().indexOf("shortelements") == 0)
						type = new BasicType(BasicType.RefType, new BasicType(BasicType.ZType, BasicType.ZType));
					else
						type = BasicType.RefType;
				}
				if (ident != null)
					switch (ident.idType) {
						case Identifier.ID_CLASS :
							break;
						case Identifier.ID_FIELD :
							if (ident.field.isExpanded())
								return BasicType.ZType;
							type = new BasicType(ident.field);
							break;
						case Identifier.ID_METHOD :
							break;
						default :
							throw new jml2b.exceptions.InternalError("TerminalForm.getBasicType(): IDENT: "
																		+ ident.getName() + " with idType: "
																		+ ident.idType);
					}
				if (postfix) {
					type = BasicType.RefType;
				}
				return type;
			case B_BTRUE :
				return BasicType.PropType;
			case Ja_LITERAL_false :
				return BasicType.BoolType;
			case Ja_LITERAL_true :
				return BasicType.BoolType;
			case Ja_NUM_INT :
				return BasicType.ZType;
				case ALL_ARRAY_ELEMS :
					return new BasicType(BasicType.ZType, BasicType.PropType);
			case FINAL_IDENT :
				if (getNodeText().equals("j_int2byte") || getNodeText().equals("j_int2char")
					|| getNodeText().equals("j_int2short"))
					return new BasicType(BasicType.ZType, BasicType.ZType);
				else if (getNodeText().equals("arraylength"))
					return new BasicType(BasicType.RefType, BasicType.ZType);
				else if (getNodeText().equals("elemtype"))
					return new BasicType(BasicType.TypesType, BasicType.TypesType);
			case Ja_LITERAL_null :
			case Ja_LITERAL_this :
			case Ja_LITERAL_super :
				return BasicType.RefType;
			case Jm_T_RESULT :
				return new BasicType(ident.field);
			case MODIFIED_FIELD :
				return new BasicType(ident.field);
			case Ja_STRING_LITERAL :
				return BasicType.RefType;
			case Ja_CHAR_LITERAL :
			case Ja_JAVA_BUILTIN_TYPE :
			default :
				throw new InternalError("TerminalForm.getBasicType() " + getNodeType());
		}

	}
	/**
	 * @return
	 */
	public Identifier getIdent() {
		return ident;
	}

	public boolean isPostfix() {
		return this.postfix;
	}
	/**
	 *  
	 */
	public Expression toExp() {
		int n = -1;
		switch (getNodeType()) {
			case Ja_IDENT :
				if (ident == null)
					return null;
				else
					return new TerminalExp(ident);
			case Ja_CHAR_LITERAL :
				n = JmlDeclParserTokenTypes.CHAR_LITERAL;
				break;
			case Ja_NUM_INT :
				n = JmlDeclParserTokenTypes.NUM_INT;
				break;
			case Ja_LITERAL_false :
				n = JmlDeclParserTokenTypes.LITERAL_false;
				break;
			case Ja_LITERAL_true :
				n = JmlDeclParserTokenTypes.LITERAL_true;
				break;
			case Ja_JAVA_BUILTIN_TYPE :
				n = JmlDeclParserTokenTypes.JAVA_BUILTIN_TYPE;
				break;
			case Ja_LITERAL_null :
				n = JmlDeclParserTokenTypes.LITERAL_null;
				break;
				case ALL_ARRAY_ELEMS :
					n = JmlDeclParserTokenTypes.STAR_ELEMS;
					break;
			case Ja_LITERAL_this :
				n = JmlDeclParserTokenTypes.LITERAL_this;
				break;
			case Ja_LITERAL_super :
				n = JmlDeclParserTokenTypes.LITERAL_super;
				break;
			case Ja_STRING_LITERAL :
				n = JmlDeclParserTokenTypes.STRING_LITERAL;
				break;
			case Jm_T_RESULT :
				n = JmlDeclParserTokenTypes.T_RESULT;
				break;
			case B_BTRUE :
				n = MyToken.BTRUE;
				break;
			default :
				return null;

		}
		return new TerminalExp(n, getNodeText());
	}

}