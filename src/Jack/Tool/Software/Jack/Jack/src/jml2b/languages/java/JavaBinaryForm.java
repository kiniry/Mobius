//******************************************************************************
//* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: 
//*
//*******************************************************************************
//* Warnings/Remarks:
//******************************************************************************/

package jml2b.languages.java;

import jml2b.exceptions.LanguageException;
import jml2b.formula.BasicType;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 */
public class JavaBinaryForm extends BinaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaBinaryForm(BinaryForm f) {
		super(f);
	}

	/**
	 * Converts into Java language a token
	 * @param n The token
	 * @param indent The current indentation value
	 * @return the string corresponding to a token. A carriage return is added
	 * when the token is an implication or a and operator
	 **/
	private static String javaConvert(int n, int indent) {
		switch (n) {
			case Ja_EQUALS_OP :
			case B_SET_EQUALS :
			case B_FUNCTION_EQUALS :
				return " == ";
			case Jm_IMPLICATION_OP :
				return jml2b.formula.Formula.indent(indent) + "==> ";
			case Ja_AND_OP :
				return jml2b.formula.Formula.indent(indent) + "&& ";
			case Jm_AND_THEN :
				return jml2b.formula.Formula.indent(indent) + "AND THEN ";
			case Ja_DIFFERENT_OP :
				return " != ";
			case Ja_OR_OP :
				return jml2b.formula.Formula.indent(indent) + "|| ";
			case Jm_OR_ELSE :
				return jml2b.formula.Formula.indent(indent) + "OR ELSE ";
			case Ja_MOD :
				return " % ";
			case Ja_ADD_OP :
				return " + ";
			case Ja_NEGATIVE_OP :
				return " - ";
			case Ja_LE_OP :
				return " <= ";
			case Ja_LESS_OP :
				return " < ";
			case Ja_GE_OP :
				return " >= ";
			case Ja_GREATER_OP :
				return " > ";
			case Ja_COMMA :
				return " , ";
			case Ja_MUL_OP :
				return " * ";
			case Ja_DIV_OP :
				return " / ";
			case B_IN :
				return " : ";
			case Jm_IS_SUBTYPE :
				return " <: ";
			default :
				return "";
				//				throw new InternalError(
				//					"BinaryForm.javaConvert " + n + "(" + toString[n] + ")");
		}
	}

	/**
	 * Converts the binary formula to a string suitable for output into
	 * the Java view.
	 * <UL>
	 * <li> <code>a <+ { b |-> c}</code> is converted in 
	 * <code>a WITH b.a == c</code>
	 * <li> <code>a <+ {b} * {c}</code> is converted in 
	 * <code>a WITH b.a == c</code>
	 * <li> otherwise <code>a <+ b</code> is converted in <code>a <+ b</code>
	 * <li> <code>j_int2short(a)</code> is converted in <code>(short) a</code>
	 * <li> <code>j_int2byte(a)</code> is converted in <code>(byte) a</code>
	 * <li> <code>j_int2char(a)</code> is converted in <code>(char) a</code>
	 * <li> <code>xxxelements(a)(b)</code> is converted in <code>a[b]</code>
	 * <li> <code>typeof(a)</code> is converted in <code>typeof(a)</code>
	 * <li> otherwise <code>a(b)</code> is converted in <code>b.a</code>
	 * <li> <code>a : b</code> is converted in <code> b a </code>
	 * <li> <code>a == true</code> is converted in <code>a</code>
	 * <li> <code>bool(a) == bool(b)</code> is converted in <code> a == b</code>
	 * <li> <code>bool(a) == false</code> is converted in <code>!a</code>
	 * <li> otherwise <code>a == b</code> is converted identically
	 * <li> <code>a <: b</code> is converted identically
	 * <li> <code>a --> b</code> is converted in <code>b</code>
	 * <li> <code>a .. b</code> is converted identically
	 * <li> <code>a * b</code> is converted identically
	 * <li> <code>a \/ b</code> is converted identically
	 * <li> <code>a <| b</code> is converted identically
	 * <li> <code>a <<| b</code> is converted identically
	 * </UL>
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		JavaTranslationResult l =
			(JavaTranslationResult) left.toLang("Java", indent);
		JavaTranslationResult r =
			(JavaTranslationResult) right.toLang("Java", indent + 3);
		switch (getNodeType()) {
			case EQUALS_ON_OLD_INSTANCES :
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				return new JavaTranslationResult(
					l + " should not be modified",
					0);
			case B_SUBSTRACTION_DOM :
				return new JavaTranslationResult(r + "\n   except on " + l, 0);
			case GUARDED_SET :
				if (right.isObvious(true))
					return l;
				else
					return new JavaTranslationResult(l + " if " + r, 0);
			case B_OVERRIDING :
				if (right.getNodeType() == B_COUPLE)
					if (left.getBasicType().getTag() == BasicType.FUNC
						&& left.getBasicType().getRtype().getTag()
							== BasicType.FUNC)
						return new JavaTranslationResult(
							"(WITH"
								+ ((BinaryForm) right).getRight().toLangDefault(indent)
								+ ")",
							0);
					else if (
						left.getBasicType().getTag() == BasicType.FUNC
							&& left.getBasicType().getLtype() == BasicType.ZType)
						return new JavaTranslationResult(
							l
								+ "(WITH "
								+ l
								+ "["
								+ ((BinaryForm) right).getLeft().toLangDefault(
									indent + 3)
								+ "] <- "
								+ ((BinaryForm) right).getRight().toLangDefault(
									indent + 3)
								+ ")",
							0);
					else
						return new JavaTranslationResult(
							l
								+ "(WITH "
								+ ((BinaryForm) right).getLeft().toLangDefault(
								    									indent + 3)
								+ "."
								+ l
								+ " <- "
								+ ((BinaryForm) right).getRight().toLangDefault(
									indent + 3)
								+ ")",
							0);
				else if (right.getNodeType() == CONSTANT_FUNCTION)
					return new JavaTranslationResult(
						l
							+ "(WITH "
							+ l
							+ "."
							+ ((BinaryForm) right).getLeft().toLangDefault(indent + 3)
							+ " <- "
							+ ((BinaryForm) right).getRight().toLangDefault(indent + 3)
							+ ")",
						0);
				else if (right.getNodeType() == CONSTANT_FUNCTION_FUNCTION) {
					return new JavaTranslationResult(
						l
							+ "(WITH "
							+ l
							+ "."
							+ ((TriaryForm) right).getLeft().toLangDefault(indent + 3)
							+ " <- "
							+ ((TriaryForm) right).getRight().toLangDefault(indent + 3)
							+ ")",
						0);
				} else
					return new JavaTranslationResult(
						l + " <+ " + r,
						JavaLanguage.priority[B_OVERRIDING]);
			case ARRAY_ACCESS :
				if (left.getNodeType() == B_APPLICATION
					&& ((BinaryForm) left).getLeft() instanceof ElementsForm)
					return new JavaTranslationResult(
						((BinaryForm) left).getRight().toLangDefault(indent)
							+ "["
							+ r
							+ "]",
						JavaLanguage.priority[getNodeType()]);
				else
					return new JavaTranslationResult(
						l + "[" + r + "]",
						JavaLanguage.priority[getNodeType()]);

			case B_APPLICATION :
				if (left == TerminalForm.$int2short)
					return new JavaTranslationResult(
						"(short) " + r,
						JavaLanguage.priority[Ja_UNARY_NUMERIC_OP]);
				if (left == TerminalForm.$int2byte)
					return new JavaTranslationResult(
						"(byte) " + r,
						JavaLanguage.priority[Ja_UNARY_NUMERIC_OP]);
				if (left == TerminalForm.$int2char)
					return new JavaTranslationResult(
						"(char) " + r,
						JavaLanguage.priority[Ja_UNARY_NUMERIC_OP]);
				//				if (left.getNodeType() == B_APPLICATION
				//					&& ((BinaryForm) left).getLeft() instanceof ElementsForm)
				//					return new JavaTranslationResult(
				//						((BinaryForm) left).getRight().toJava(indent)
				//							+ "["
				//							+ r
				//							+ "]");
				if (left instanceof ElementsForm)
					return r;
				if (left == TerminalForm.$arraylength)
					return new JavaTranslationResult(
						right.toLangDefault(indent) + ".length",
						JavaLanguage.priority[Ja_IDENT]);
				if (left instanceof TerminalForm) {
					if (((TerminalForm) left)
						.getNonAmbiguousName()
						.equals("j_and"))
						return new JavaTranslationResult(
							((BinaryForm) right).getLeft().toLangDefault(indent)
								+ " & "
								+ ((BinaryForm) right).getRight().toLangDefault(
									indent + 3),
							7);
					if (((TerminalForm) left)
						.getNonAmbiguousName()
						.equals("j_or"))
						return new JavaTranslationResult(
							((BinaryForm) right).getLeft().toLangDefault(indent)
								+ " | "
								+ ((BinaryForm) right).getRight().toLangDefault(
									indent + 3),
							5);
					if (((TerminalForm) left)
						.getNonAmbiguousName()
						.equals("j_shl"))
						return new JavaTranslationResult(
							((BinaryForm) right).getLeft().toLangDefault(indent)
								+ " << "
								+ ((BinaryForm) right).getRight().toLangDefault(
									indent + 3),
							10);
					if (((TerminalForm) left)
						.getNonAmbiguousName()
						.equals("j_shr"))
						return new JavaTranslationResult(
							((BinaryForm) right).getLeft().toLangDefault(indent)
								+ " >> "
								+ ((BinaryForm) right).getRight().toLangDefault(
									indent + 3),
							10);
				}
				if (left.getBasicType().getTag() == BasicType.FUNC
					&& left.getBasicType().getRtype().getTag() == BasicType.FUNC)
					return new JavaTranslationResult(r + "" + l, 0);
				if (left != TerminalForm.$typeof)
					return new JavaTranslationResult(
						r + "." + l,
						JavaLanguage.priority[Ja_IDENT]);

				return new JavaTranslationResult(l + "(" + r + ")", 0);

			case LOCAL_VAR_DECL :
				return new JavaTranslationResult(r + " " + l, 0);

			case Ja_EQUALS_OP :
			case B_SET_EQUALS :
			case B_FUNCTION_EQUALS :
				if (right.getNodeType() == Ja_LITERAL_true) {
					if (left.getNodeType() == B_BOOL)
						return ((UnaryForm) left).getExp().toLang(
							"Java",
							indent);
					else
						return left.toLang("Java", indent);
				} else if (left.getNodeType() == B_BOOL) {
/*					if (right.getNodeType() == B_BOOL)
						return new JavaTranslationResult(
							((UnaryForm) left).getExp().toJava(indent)
								+ " == "
								+ ((UnaryForm) right).getExp().toJava(indent),
							JavaLanguage.priority[Ja_EQUALS_OP]);
					else*/ if (right.getNodeType() == Ja_LITERAL_false)
						return new JavaTranslationResult(
							"!" + ((UnaryForm) left).getExp().toLangDefault(indent),
							JavaLanguage.priority[Ja_LNOT]);
				}
				break;

			case IS_MEMBER_FIELD :
				return r;

			case B_INTERVAL :
				return new JavaTranslationResult(
					l + " .. " + r,
					JavaLanguage.priority[getNodeType()]);

			case B_UNION :
				return new JavaTranslationResult(
					l + " \\/ " + r,
					JavaLanguage.priority[getNodeType()]);

			case INTERSECTION_IS_NOT_EMPTY :
				return new JavaTranslationResult(
					l + " intersected with " + r + " is not empty",
					0);
		}

		String ls = l.toUniqString();
		String rs = r.toUniqString();

		if (l.getPriority() < JavaLanguage.priority[getNodeType()])
			ls = "(" + ls + ")";

		if (r.getPriority() <= JavaLanguage.priority[getNodeType()])
			rs = "(" + rs + ")";

		return new JavaTranslationResult(
			ls + javaConvert(getNodeType(), indent) + rs,
			JavaLanguage.priority[getNodeType()]);
	}
}
