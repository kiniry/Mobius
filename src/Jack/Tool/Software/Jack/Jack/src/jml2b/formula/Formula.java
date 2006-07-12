//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Formula.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.io.IOException;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.*;
import jml2b.languages.ITranslationResult;
import jml2b.languages.Languages;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Field;
import jml2b.structure.java.IJmlFile;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;
import jml2b.util.Profiler;

/**
 * This class describes a formula.
 * A formula is the content of a lemma : an hypothesis or a goal.
 * @author L. Burdy
 */
abstract public class Formula
	extends Profiler
	implements IFormToken, Serializable {

	/** the formula for <code>null</code> */
	public static final Formula $null = new TerminalForm(Ja_LITERAL_null, "null");
	/** the formula for <code>false</code> */
	public static final Formula $false = new TerminalForm(Ja_LITERAL_false);
	/** the formula for <code>true</code> */
	public static final Formula $true = new TerminalForm(IFormToken.Ja_LITERAL_true);
	/** the formula for <code>True</code> */
	public static final Formula $True = new TerminalForm(IFormToken.B_BTRUE);
	/** the formula for expressing the result of a method */
	public static final Formula $result = new TerminalForm(IFormToken.Jm_T_RESULT);
	/** the formula for <code>this</code> */
	public static final Formula $this = new TerminalForm(IFormToken.Ja_LITERAL_this, "this");

	
	/**
	 * Returns the disjunctive formula between the two parameters.
	 * @param s1 left disjonctive formula
	 * @param s2 right disjonctive formula
	 * @return the formula <code>s1 || s2</code>
	 **/
	public static Formula or(Formula s1, Formula s2) {
		return new BinaryForm(Ja_OR_OP, s1, s2);
//		return new MethodCallForm("or", comma(s1, s2), null, "", 
//				new TTypeForm(IFormToken.T_TYPE, new Type(Type.T_BOOLEAN)));
	}
	
	public static Formula diff(Formula s1, Formula s2) {
		return new BinaryForm(Ja_DIFFERENT_OP, s1, s2);
	}

	public static Formula apply(Formula s1, Formula s2) {
		return new BinaryForm(
				IFormToken.B_APPLICATION, s1, s2);
	}
	
	/**
	 * The same as {@link #apply(Formula, Formula)}, but
	 * s2 can be <code>null</code>.
	 * @param s1 
	 * @param s2
	 * @return s1 applied to s2 or s1 if s2 is null.
	 */
	public static Formula apply_safe(Formula s1, Formula s2) {
		if(s2 == null) {
			return s1;
		}
		else {
			return new BinaryForm(
					IFormToken.B_APPLICATION, s1, s2);
		}
	}
	public static Formula equals(Formula s1, Formula s2) {
		return new BinaryForm(IFormToken.Ja_EQUALS_OP, s1, s2);
	}
	/**
	 * Returns the formula corresponding to a field declaration.
	 * @param f Field to declare.
	 * @return
	 */
	public static Formula declarField(Field f) {
		if (f.getType().isBuiltin())
			return new BinaryForm(
				LOCAL_VAR_DECL,
				new TerminalForm(new Identifier(f)),
				new TTypeForm(IFormToken.T_TYPE, f.getType()));
		else
			return and(
					new BinaryForm(
							LOCAL_VAR_DECL,
							new TerminalForm(new Identifier(f)),
							TerminalForm.$References),
							and(
					new BinaryForm(
						B_IN,
						new TerminalForm(new Identifier(f)),
						new BinaryForm(
							B_UNION,
							TerminalForm.$instances,
							new UnaryForm(
								B_ACCOLADE,
								$null))),
					implies(
						diff(
							new TerminalForm(new Identifier(f)), $null),
						new BinaryForm(
							Jm_IS_SUBTYPE,
							apply(
								TerminalForm.$typeof,
								new TerminalForm(new Identifier(f))),
							new TTypeForm(
								IFormToken.Jm_T_TYPE,
								f.getType())))));

	}

	/**
	 * Returns the conjunctive formula between the two parameters.
	 * @param s1 left conjonctive formula
	 * @param s2 right conjonctive formula
	 * @return the formula <code>s1 && s2</code>
	 **/
	public static Formula and(Formula s1, Formula s2) {
//		return new MethodCallForm("and", comma(s1, s2), null, "", 
//				new TTypeForm(IFormToken.T_TYPE, new Type(Type.T_BOOLEAN)));
		return new BinaryForm(Ja_AND_OP, s1, s2);
	}

	/**
	 * 
	 * @param s1
	 * @param s2
	 * @return the binary form of type comma containing s1 and s2
	 */
	public static Formula comma(Formula s1, Formula s2) {
		return new BinaryForm(Ja_COMMA, s1, s2);
	}
	/**
	 * The same as {@link #comma(Formula, Formula)}, but test if one of the formula is null.
	 * 
	 * @param s1
	 * @param s2
	 * @return the binary form of type comma containing s1 and s2, 
	 * 		otherwise s1 if s2 is null or s2 if s1 is null
	 */
	public static Formula comma_safe(Formula s1, Formula s2) {
		if(s1 == null) {
			return s2;
		}
		else if (s2 == null) {
			return s1;
		}
		return new BinaryForm(Ja_COMMA, s1, s2);
	}
	
	/**
	 * Returns the negation of the parameter.
	 * @param s1 negated formula
	 * @return the formula <code>! s1</code>
	 **/
	public static UnaryForm not(Formula s1) {
		return new UnaryForm(Ja_LNOT, s1);
	}

	/**
	 * Returns the implicative formula between the two parameters.
	 * @param s1 left implicative formula
	 * @param s2 right implicative formula
	 * @return the formula <code>s1 ==> s2</code>
	 **/
	public static Formula implies(Formula s1, Formula s2) {
		return new BinaryForm(Jm_IMPLICATION_OP, s1, s2);
	}

	/**
	 * Create a formula from a token read into a stream.
	 * @param config The current configuration
	 * @param s The input stream
	 * @param fi The JML file corresponding to the input stream.
	 * @return a new formula instanciated with the read token, ready to be 
	 * parsed.
	 * @throws IOException if the end of the stream is reached before the 
	 * formula has been read
	 * @throws LoadException if the read token is unknown.
	 **/
	/*@
	  @ requires s != null;
	  @ ensures \result != null;
	  @*/
	public static Formula create(
		IJml2bConfiguration config,
		JpoInputStream s,
		IJmlFile fi)
		throws IOException, LoadException {
		byte nodeType;
		switch (nodeType = s.readByte()) {
			case DECL_PURE_METHOD :
				return new DeclPureMethodForm(config, fi, s);
			case METHOD_CALL :
				return new MethodCallForm(config, fi, s);
			case Ja_QUESTION :
			case CONSTANT_FUNCTION_FUNCTION :
			case ARRAY_RANGE :
			case NEW_OBJECT :
			case B_ARRAY_EQUALS :
				return new TriaryForm(config, fi, nodeType, s);
			case B_SUBSTRACTION_DOM :
			case Jm_IS_SUBTYPE :
			case B_OVERRIDING :
			case B_UNION :
			case INTERSECTION_IS_NOT_EMPTY :
			case CONSTANT_FUNCTION :
			case B_INTERVAL :
			case B_APPLICATION :
			case ARRAY_ACCESS :
			case B_IN :
			case LOCAL_VAR_DECL :
				case LOCAL_ELEMENTS_DECL :
			case Ja_MOD :
			case B_COUPLE :
			case Ja_COMMA :
			case Ja_ADD_OP :
			case Ja_NEGATIVE_OP :
			case Ja_MUL_OP :
			case Ja_DIV_OP :
			case Ja_EQUALS_OP :
			case Ja_DIFFERENT_OP :
			case Ja_AND_OP :
			case Jm_AND_THEN :
			case Ja_OR_OP :
			case Jm_OR_ELSE :
			case Ja_LE_OP :
			case Ja_LESS_OP :
			case Ja_GE_OP :
			case Ja_GREATER_OP :
			case Jm_IMPLICATION_OP :
			case GUARDED_SET :
			case EQUALS_ON_OLD_INSTANCES :
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
			case B_FUNCTION_EQUALS :
			case B_SET_EQUALS :
			case IS_MEMBER_FIELD :
			case ALL_ARRAY_ELEMS :
				return new BinaryForm(config, fi, nodeType, s);
			case Jm_FORALL :
			case Jm_EXISTS :
				return new QuantifiedForm(config, fi, nodeType, s);
			case B_ACCOLADE :
			case B_BOOL :
			case Ja_UNARY_NUMERIC_OP :
			case Ja_LNOT :
			case Jm_T_OLD :
			case B_DOM :
			case T_VARIANT_OLD :
			case IS_ARRAY :
			case IS_STATIC_FIELD :
				return new UnaryForm(config, fi, nodeType, s);
			case Ja_IDENT :
				{
					String tmp = s.readUTF();
					BasicType bt = new BasicType(s);
					if (tmp.equals("typeof"))
						return TerminalForm.$typeof;
					else if (tmp.equals("instances"))
						return TerminalForm.$instances;
					//					else if (tmp.equals("arraylength"))
					//						return TerminalForm.getArraylength(config);
					else if (tmp.indexOf("intelements") == 0)
						return new ElementsForm(tmp, Type.T_INT);
					else if (tmp.indexOf("shortelements") == 0)
						return new ElementsForm(tmp, Type.T_SHORT);
					else if (tmp.indexOf("booleanelements") == 0)
						return new ElementsForm(tmp, Type.T_BOOLEAN);
					else if (tmp.indexOf("byteelements") == 0)
						return new ElementsForm(tmp, Type.T_BYTE);
					else if (tmp.indexOf("charelements") == 0)
						return new ElementsForm(tmp, Type.T_CHAR);
					else if (tmp.indexOf("refelements") == 0)
						return new ElementsForm(tmp, Type.T_REF);
					else
						return new LoadedTerminalForm(fi, nodeType, tmp, bt, s);
				}
			case FINAL_IDENT :
				{
					String tmp = s.readUTF();
					BasicType bt = new BasicType(s);
					if (tmp.equals("REFERENCES"))
						return TerminalForm.$References;
					else if (tmp.equals("elemtype"))
						return TerminalForm.$elemtype;
					else if (tmp.equals("j_int2short"))
						return TerminalForm.$int2short;
					else if (tmp.equals("j_int2byte"))
						return TerminalForm.$int2byte;
					else if (tmp.equals("j_int2char"))
						return TerminalForm.$int2char;
					else
						return new LoadedTerminalForm(fi, nodeType, tmp, bt, s);
				}
			case B_BTRUE :
			case Ja_CHAR_LITERAL :
			case Ja_NUM_INT :
			case Ja_LITERAL_false :
			case Ja_LITERAL_true :
			case Ja_JAVA_BUILTIN_TYPE :
			case Ja_LITERAL_null :
			case Ja_LITERAL_this :
			case Ja_LITERAL_super :
			case Ja_STRING_LITERAL :
			case MODIFIED_FIELD :
			case Jm_T_RESULT :
				{
					String tmp = s.readUTF();
					BasicType bt = new BasicType(s);
					return new LoadedTerminalForm(fi, nodeType, tmp, bt, s);
				}
			case Jm_T_TYPE :
			case T_TYPE :
				return new LoadedTTypeForm(config, fi, nodeType, s.readUTF(), s);
			default :
				throw new LoadException("Formula.create " + nodeType);
		}
	}

	/**
	 * Returns the string containing white spaces corresponding to an 
	 * indentation
	 * @param i The indentation number
	 * @return a string with a carriage return and <code>i</code> white spaces.
	 **/
	public static String indent(int i) {
		String res = "\n";
		for (int j = 0; j < i; j++)
			res += " ";
		return res;
	}

	/**
	 * token describing this formula.
	 **/
	private byte nodeType;

	/*@
	  @ protected invariant nodeType != null;
	  @ protected invariant nodeType == Ja_EQUAL_OP 
	  @                     ==> \typeof(this) <: \type(BinaryForm);
	  @ protected invariant nodeType == Jm_T_TYPE 
	  @                     ==> \typeof(this) <: \type(TTypeForm);
	  @ protected invariant nodeType == T_CALLED_OLD 
	  @                     ==> \typeof(this) <: \type(UnaryForm);
	  @ protected invariant (\forall Formula f; nodeType == f.nodeType 
	  @                                        ==> \typeof(this) == \typeof(f));
	  @*/

	/**
	 * Creates a formula with a given node type.
	 * @param nodeType the node type
	 **/
	Formula(byte nodeType) {
		this.nodeType = nodeType;
	}

	/**
	 * Returns the type of a formula
	 * @return The basic type of ta formula.
	 */
	public abstract BasicType getBasicType();

	/**
	 * Clones the formula.
	 * @return the cloned formula
	 **/
	public abstract Object clone();

	/**
	 * Collects all the indentifier of a formula to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	public abstract void processIdent();

	/** 
	 * Replaces <code>this</code> with the parameter in the expression.
	 * @param b expression on which the method where the expression occurs is 
	 * called.
	 * @return the modified expression
	 **/
	public abstract Formula instancie(Formula b);

	/**
	 * Collects the fields that occur in the formula.
	 * @param fields The set a collected fields.
	 **/
	public abstract void getFields(Set fields);

	/**
	 * Applies a substitution on a formula.
	 * @param a the substituted formula
	 * @param b the new formula
	 * @param subInCalledOld specify whether the substitution should also be 
	 * applied in the <i>called old</i> construction
	 * @return the formula when the substitution has been applied.
	 **/
	/*@
	  @ requires a != null;
	  @ ensures \result != null;
	  @*/
	public abstract Formula sub(Formula a, Formula b, boolean subInCalledOld);

	/**
	 * Suppress the <i>called old</i> pragmas.
	 * <i>old</i> pragma are substitued with <i>called old</i> into the
	 * specification of a called method in manner to be differentiated from
	 * the <i>old</i> pragma of the current method.
	 * After the treatment, the <i>called old</i> pragmas are suppressed.
	 * @return the formula with suppressed <i>called old</i> pragmas
	 **/
	public abstract Formula suppressSpecialOld(int token);

	/**
	 * Applies a substitution on a formula.
	 * @param a the substituted string correspondingto an identifier
	 * @param b the new formula
	 * @return the formula when the substitution has been applied.
	 **/
	//@ ensures \result != null;
	public abstract Formula subIdent(String a, Formula b);

	/**
	 * Returns whether the formula equals the parameter.
	 * @param f the checked parameter
	 * @return <code>true</code> if the formula syntaxically equals the 
	 * parameter, <code>false</code> otherwise
	 **/
	public abstract boolean equals(Object f);

	/**
	 * Returns whether the formula corresponds to a read formula.
	 * @param f a read formula coming from a jpo file
	 * @return <code>true</code> if the formula equals to the read formula,
	 * <code>false</code> otherwise.
	 * @throws MergeException
	 **/
	public abstract boolean is(Formula f);

	/**
	 * Returns whether a formula is obvious.
	 * @return <code>true</code> if the formula is considered as obvious,
	 * <code>false</code> otherwise
	 **/
	public abstract boolean isObvious(boolean atTheEnd);

	/**
	 * Saves the formula in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param config 
	 * @param s the ouputstream corresponding to a jpo file
	 * @param jf 
	 * @throws IOException when the formula cannot be saved.
	 **/
	public abstract void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException;

	/**
	 * Annotates all the fields that appear in the formula to declare them in 
	 * the Atelier B files.
	 **/
	public abstract void garbageIdent();

	public abstract int contains(Vector selectedFields);

	/**
	 * Encapsulates given parameters into an <code>old</code> pragma.
	 * @param signature the signature of a called method
	 * @return the formula when the parameters have been encapsulated
	 **/
	//@ ensures \result != null;
	public Formula oldParam(Vector signature) {
		Formula res = (Formula) clone();
		Enumeration e = signature.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			Formula s = new UnaryForm(Jm_T_OLD, new TerminalForm(new Identifier(f)));
			res = res.subIdent(f.getBName(), s);
		}
		return res;
	}

	/**
	 * Translates the formula into the Java language
	 * @deprecated Use toLangDefault(indent) instead)
	 * @param indent The current indentation
	 * @return the string corresponding to the translated formula.
	 **/
	public String toJava(int indent) {
		return toLangDefault(indent);
	}

	/**
	 * Translates the formula into the Java language
	 * @param indent The current indentation
	 * @return the string corresponding to the translated formula.
	 **/
	public String toLangDefault(int indent) {
		try {
			return toLang("Java", indent).toUniqString();
		} catch (LanguageException le) {
			throw new InternalError(le.getMessage());
		}
	}
	/**
	 * Translates the formula into a given language.
	 * @param language The language in which the formula should be translated.
	 * @param indent The current indentation
	 * @return the result of the translation
	 * @throws LanguageException when the language is unknown.
	 */
	public ITranslationResult toLang(String language, int indent)
		throws LanguageException {
		return Languages.getLanguageClass(language).formulaFactory(
			this).toLang(
			indent);
	}

	/**
	 * Applies a substitution on a formula.
	 * @param a the substituted field
	 * @param b the new field
	 * @param subInCalledOld specify whether the substitution should also be 
	 * applied in the <i>called old</i> construction
	 * @return the formula when the substitution has been applied.
	 **/
	public Formula sub(Field a, Field b, boolean subInCalledOld) {
		Formula f1 = new TerminalForm(new Identifier(a));
		Formula f2 = new TerminalForm(new Identifier(b));
		return sub(f1, f2, subInCalledOld);

	}

	/**
	 * Renames the fields belonging to the parameter list with new names.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current formula renamed
	 * @see jml2b.pog.Proofs#renameParam(Parameters, Vector)
	 **/
	private Formula renameParam(
		Enumeration signature,
		Enumeration newSignature) {
		if (signature.hasMoreElements()) {
			Field f = (Field) signature.nextElement();
			TerminalForm f1 = new TerminalForm(new Identifier(f));
			Object o = newSignature.nextElement();
			Formula f2;
			if (o instanceof String)
				f2 = new TerminalForm((String) o);
			else
				f2 = (Formula) o;
			return renameParam(signature, newSignature).sub(f1, f2, true);
		} else
			return (Formula) clone();
	}

	/**
	 * Renames the fields belonging to the parameter list with new names.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current formula renamed
	 * @see jml2b.pog.Proofs#renameParam(Parameters, Vector)
	 **/
	public Formula renameParam(IAParameters signature, Vector newSignature)
		throws PogException {
		if (signature instanceof Parameters)
		return renameParam(
			((Parameters) signature).signature.elements(),
			newSignature.elements());
		else
			return this;
//		else
//			throw new jml2b.exceptions.InternalError("Formula.renameParam");
	}

	/**
	 * Returns whether a formula corresponds to <i>bfalse</i>
	 * @return <code>true</code> when the formula is <code>false == true</code>
	 * or <code>true == false</code>, <code>false</code> otherwise.
	 **/
	public boolean isBFalse() {
		return nodeType == Ja_EQUALS_OP
			&& ((((BinaryForm) this).getLeft().nodeType == Ja_LITERAL_false
				&& ((BinaryForm) this).getRight().nodeType == Ja_LITERAL_true)
				|| (((BinaryForm) this).getLeft().nodeType == Ja_LITERAL_true
					&& ((BinaryForm) this).getRight().nodeType
						== Ja_LITERAL_false));
	}

	/** 
	 * Returns whether a formula matches with an equality with 
	 * <code>null</code>
	 * @return <code>true</code> if th
							new TerminalForm(Ja_LITERAL_null, "null")e formula matches with 
	 * <code>a == null</code>, <code>false</code> otherwise.
	 **/
	public boolean matchAEqualsNull() {
		return nodeType == Ja_EQUALS_OP
			&& ((BinaryForm) this).getRight().nodeType == Ja_LITERAL_null;
	}

	/** 
	 * Converts comma separated formulas into a set of formulas.
	 * @return the vector containing comme separated formulas
	 * @see BinaryForm#toVector()
	 **/
	public Vector toVector() {
		Vector res = new Vector();
		res.add(this);
		return res;
	}

	/**
	 * Applies successive domain restriction to the formula
	 * @param df set of formula from which the formula should be restricted.
	 * @return the formula with domain restricted with the set of given 
	 * formulas
	 **/
	public FormulaWithSpecMethodDecl domainRestrict(Vector df) {
		FormulaWithSpecMethodDecl res = new FormulaWithSpecMethodDecl(this);
		Enumeration e = df.elements();
		while (e.hasMoreElements()) {
			FormulaWithSpecMethodDecl f = (FormulaWithSpecMethodDecl) e.nextElement();
			res = new FormulaWithSpecMethodDecl(f, res, new BinaryForm(B_SUBSTRACTION_DOM, f.getFormula(), res.getFormula()));
		}
		return res;
	}

	/**
	 * Returns the nodeType.
	 * @return byte
	 */
	public byte getNodeType() {
		return nodeType;
	}
	public String toString() {
		return toLangDefault(0);
	}
	static final long serialVersionUID = 2912250853358401101L;

}