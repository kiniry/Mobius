//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.statement.Statement;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BBinaryForm extends BinaryForm implements ITranslatable {

	static final long serialVersionUID = 2326609905613455458L;
	String lang;

	BBinaryForm(String lang, BinaryForm f) {
		super(f);
		this.lang = lang;
	}

	/**
	 * Converts in B a <code>EQUALS_SUBSTRACTION_DOM</code> node
	 * @param subs The current substraction to apply to the dom of the
	 * restricted formula.
	 * @return the converted formula
	 **/
	private ITranslationResult equalsSubsDomToB(String subs, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_FUNCTION_EQUALS :
				{
					String l = left.toLang(lang, indent).toUniqString();
					String r = right.toLang(lang, indent).toUniqString();
					return new BTranslationResult(
						"dom("
							+ l
							+ ") = dom("
							+ r
							+ ") &"
							+ subs
							+ " <<| "
							+ l
							+ " = "
							+ subs
							+ " <<| "
							+ r);
				}
			case EQUALS_ON_OLD_INSTANCES :
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				String l = getLeft().toLang(lang, indent).toUniqString();
				String r = getRight().toLang(lang, indent).toUniqString();
				return new BTranslationResult(
					"instances /\\ dom("
						+ l
						+ ") = instances /\\ dom("
						+ r
						+ ") &"
						+ subs
						+ " <<| (instances <|"
						+ l
						+ ") = "
						+ subs
						+ " <<| ( instances <|"
						+ r
						+ ")");
			case B_SUBSTRACTION_DOM :
				if (right instanceof BinaryForm)
					return (
						new BBinaryForm(
							lang,
							(BinaryForm) right)).equalsSubsDomToB(
						left.toLang(lang, indent).toUniqString()
							+ " <<| "
							+ subs,
						indent);
				else
					return (
						new BTriaryForm(
							lang,
							(TriaryForm) right)).equalsSubsDomToB(
						left.toLang(lang, indent).toUniqString()
							+ " <<| "
							+ subs,
						indent);

			default :
				throw new InternalError(
					"BinaryForm.equalsSubsDomToB(String) bad node type: "
						+ getNodeType());
		}
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = "";
		switch (getNodeType()) {
			case EQUALS_ON_OLD_INSTANCES :
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				return new BTranslationResult(
					"instances /\\ dom("
						+ left.toLang(lang, indent).toUniqString()
						+ ") = instances /\\ dom("
						+ right.toLang(lang, indent).toUniqString()
						+ ") & instances <|"
						+ left.toLang(lang, indent).toUniqString()
						+ " = instances <|"
						+ right.toLang(lang, indent).toUniqString());
			case B_SUBSTRACTION_DOM :
				if (right instanceof BinaryForm)
					return (
						new BBinaryForm(
							lang,
							(BinaryForm) right)).equalsSubsDomToB(
						left.toLang(lang, indent).toUniqString(),
						indent);
				else
					return (
						new BTriaryForm(
							lang,
							(TriaryForm) right)).equalsSubsDomToB(
						left.toLang(lang, indent).toUniqString(),
						indent);
			case GUARDED_SET :
				if (right.getNodeType() == IFormToken.B_BTRUE
					|| (right.getNodeType() == Ja_EQUALS_OP
						&& ((BinaryForm) right).getLeft().getNodeType()
							== Ja_LITERAL_true
						&& ((BinaryForm) right).getRight().getNodeType()
							== Ja_LITERAL_true))
					return left.toLang(lang, indent);
				else {
					String v = Statement.fresh();
					return new BTranslationResult(
						"SET("
							+ v
							+ ").("
							+ v
							+ " : "
							+ left.toLang(lang, indent).toUniqString()
							+ " & "
							+ right.toLang(lang, indent).toUniqString()
							+ ")");
				}
			case Ja_ADD_OP :
				try {
					int i =
						Integer
							.decode(left.toLang(lang, indent).toUniqString())
							.intValue();
					int j =
						Integer
							.decode(right.toLang(lang, indent).toUniqString())
							.intValue();
					return new BTranslationResult("" + (i + j));
				} catch (NumberFormatException nfe) {
					break;
				}
			case Ja_NEGATIVE_OP :
				try {
					int i =
						Integer
							.decode(left.toLang(lang, indent).toUniqString())
							.intValue();
					int j =
						Integer
							.decode(right.toLang(lang, indent).toUniqString())
							.intValue();
					return new BTranslationResult("" + (i - j));
				} catch (NumberFormatException nfe) {
					break;
				}
			case Ja_MUL_OP :
				try {
					int i =
						Integer
							.decode(left.toLang(lang, indent).toUniqString())
							.intValue();
					int j =
						Integer
							.decode(right.toLang(lang, indent).toUniqString())
							.intValue();
					return new BTranslationResult("" + (i * j));
				} catch (NumberFormatException nfe) {
					break;
				}
			case Ja_DIV_OP :
				try {
					int i =
						Integer
							.decode(left.toLang(lang, indent).toUniqString())
							.intValue();
					int j =
						Integer
							.decode(right.toLang(lang, indent).toUniqString())
							.intValue();
					return new BTranslationResult("" + (i / j));
				} catch (NumberFormatException nfe) {
					break;
				} catch (ArithmeticException ae) {
					break;
				}
			case Jm_IS_SUBTYPE :
				return new BTranslationResult(
					left.toLang(lang, indent).toUniqString()
						+ ": subtypes[{"
						+ right.toLang(lang, indent).toUniqString()
						+ "}]");
			case Ja_DIFFERENT_OP :
				return (
					new UnaryForm(
						Ja_LNOT,
						new BinaryForm(Ja_EQUALS_OP, left, right))).toLang(
					lang,
					indent);
			case Ja_GREATER_OP :
				return (
					new BinaryForm(
						Ja_LE_OP,
						new BinaryForm(
							Ja_ADD_OP,
							right,
							new TerminalForm(Ja_NUM_INT, "1")),
						left)).toLang(
					lang,
					indent);
			case Ja_GE_OP :
				return (new BinaryForm(Ja_LE_OP, right, left)).toLang(
					lang,
					indent);
			case Ja_LESS_OP :
				return (
					new BinaryForm(
						Ja_LE_OP,
						new BinaryForm(
							Ja_ADD_OP,
							left,
							new TerminalForm(Ja_NUM_INT, "1")),
						right)).toLang(
					lang,
					indent);
			case B_COUPLE :
				res = "{";
				if (BLanguage.priority[left.getNodeType()]
					< BLanguage.priority[getNodeType()]) {
					res += "(" + left.toLang(lang, indent).toUniqString() + ")";
				} else
					res += left.toLang(lang, indent).toUniqString();
				res += " |-> ";
				if (BLanguage.priority[right.getNodeType()]
					<= BLanguage.priority[getNodeType()]) {
					res += "("
						+ right.toLang(lang, indent).toUniqString()
						+ ")";
				} else
					res += right.toLang(lang, indent).toUniqString();

				return new BTranslationResult(res + "}");
			case CONSTANT_FUNCTION :
				if (BLanguage.priority[left.getNodeType()]
					< BLanguage.priority[getNodeType()]) {
					res = "(" + left.toLang(lang, indent).toUniqString() + ")";
				} else
					res = left.toLang(lang, indent).toUniqString();

				return new BTranslationResult(
					res
						+ " * {"
						+ right.toLang(lang, indent).toUniqString()
						+ "}");
			case INTERSECTION_IS_NOT_EMPTY :
				return new BTranslationResult(
					left.toLang(lang, indent).toUniqString()
						+ "/\\"
						+ right.toLang(lang, indent).toUniqString()
						+ " /= {}");
				case ALL_ARRAY_ELEMS :
					return new BTranslationResult("ran(" +left.toLang(lang, indent).toUniqString() + "(" + right.toLang(lang, indent).toUniqString() + "))");
				
		}
		if (BLanguage.priority[left.getNodeType()]
			< BLanguage.priority[getNodeType()]) {
			res = "(" + left.toLang(lang, indent).toUniqString() + ")";
		} else
			res = left.toLang(lang, indent).toUniqString();

		res += BBinaryForm.bConvert(getNodeType(), 0);

		if (right != null) {
			if (BLanguage.priority[right.getNodeType()]
				<= BLanguage.priority[getNodeType()]) {
				res += "(" + right.toLang(lang, indent).toUniqString() + ")";
			} else
				res += right.toLang(lang, indent).toUniqString();
		}
		return new BTranslationResult(res);
	}

	/**
	 * Returns the string in the B language corresponding to a token.
	 * @param n The token
	 * @param indent The current indentation value
	 * @return the B operator
	 * @throws InternalError when the token is unknown
	 **/
	public static String bConvert(int n, int indent) {
		switch (n) {
			case IFormToken.Ja_EQUALS_OP :
			case B_SET_EQUALS :
			case B_FUNCTION_EQUALS :
				return " = ";
			case IFormToken.Jm_IMPLICATION_OP :
				return Formula.indent(indent) + "=> ";
			case IFormToken.Ja_AND_OP :
			case Jm_AND_THEN :
				return Formula.indent(indent) + "& ";
			case IFormToken.Ja_DIFFERENT_OP :
				return " /= ";
			case IFormToken.Ja_OR_OP :
			case Jm_OR_ELSE :
				return " or ";
			case IFormToken.Ja_MOD :
				return " mod ";
			case IFormToken.B_APPLICATION :
			case ARRAY_ACCESS :
				return "";
			case IFormToken.Ja_ADD_OP :
				return " + ";
			case IFormToken.Ja_NEGATIVE_OP :
				return " - ";
			case IFormToken.LOCAL_VAR_DECL :
			case IFormToken.LOCAL_ELEMENTS_DECL :
			case IFormToken.B_IN :
				return " : ";
			case IFormToken.IS_MEMBER_FIELD :
				return " +-> ";
			case IFormToken.B_OVERRIDING :
				return " <+ ";
			case IFormToken.B_INTERVAL :
				return " .. ";
				//			case FormToken.CONSTANT_FUNCTION :
				//				return " * ";
			case IFormToken.B_UNION :
				return " \\/ ";
			case IFormToken.Ja_LE_OP :
				return " <= ";
			case IFormToken.Ja_LESS_OP :
				return " < ";
			case IFormToken.Ja_GE_OP :
				return " >= ";
			case IFormToken.Ja_GREATER_OP :
				return " > ";
			case IFormToken.Ja_COMMA :
				return " , ";
			case IFormToken.Ja_MUL_OP :
				return " * ";
			case IFormToken.Ja_DIV_OP :
				return " / ";
			default :
				throw new InternalError(
					"BinaryForm.bConvert "
						+ n
						+ "("
						+ IFormToken.toString[n]
						+ ")");
		}
	}
}
