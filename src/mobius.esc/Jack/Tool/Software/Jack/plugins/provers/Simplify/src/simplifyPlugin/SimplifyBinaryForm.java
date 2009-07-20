//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyBinaryForm extends BinaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = -5564072961649941336L;
	/** 
	 * List of constant functions for which the B application will not
	 * be converted using select for simplify output.
	 */
	public static final String[] JACK_CONSTANT_FCT =
		{
			"j_shl",
			"j_shr",
			"j_ushr",
			"j_and",
			"j_or",
			"j_xor",
			"j_int2byte",
			"j_int2char",
			"j_int2short" };

	SimplifyBinaryForm(BinaryForm f) {
		super(f);
	}

	static SimplifyTranslationResult in(
		SimplifyTranslationResult left,
		SimplifyTranslationResult right) {
		return new SimplifyTranslationResult(
			left,
			right,
			"(EQ ("
				+ right.toUniqString()
				+ " "
				+ left.toUniqString()
				+ ") |@true|)");
	}

	/**
	 * Converts the content of this AND node into simplify output, suppressing
	 * the unneeded ANDs (Simplify's and is nary and not binary).
	 */
	//@ requires nodeType.n() == B_AND_OP;
	private SimplifyTranslationResult appendSimplifyAnd(int indent)
		throws LanguageException {
		SimplifyTranslationResult r1 = null;
		SimplifyTranslationResult r2 = null;
		if (left.getNodeType() == Ja_AND_OP
			|| left.getNodeType() == Jm_AND_THEN) {
			SimplifyBinaryForm bf = new SimplifyBinaryForm((BinaryForm) left);
			r1 = bf.appendSimplifyAnd(indent);
		} else {
			r1 = (SimplifyTranslationResult) left.toLang("Simplify", indent);
		}
		if (right.getNodeType() == Ja_AND_OP
			|| right.getNodeType() == Jm_AND_THEN) {
			SimplifyBinaryForm bf = new SimplifyBinaryForm((BinaryForm) right);
			r2 = bf.appendSimplifyAnd(indent);
		} else {
			r2 = (SimplifyTranslationResult) right.toLang("Simplify", indent);
		}
		return new SimplifyTranslationResult(
			r1,
			r2,
			r1.toUniqString() + " " + r2.toUniqString());
	}

	private SimplifyTranslationResult appendSimplifyBApplication(int indent)
		throws LanguageException {
		// check if the left child is an identifier corresponding
		// to a known function
		if (left instanceof ElementsForm) {
			String x = SimplifyLanguage.newName();
			String name = SimplifyLanguage.newName();
			SimplifyTranslationResult str1 =
				(SimplifyTranslationResult) left.toLang("Simplify", indent);
			SimplifyTranslationResult str2 =
				(SimplifyTranslationResult) right.toLang("Simplify", indent);
			return new SimplifyTranslationResult(
				str1,
				str2,
				"(FORALL ("
					+ x
					+ ") (EQ (select "
					+ name
					+ " "
					+ x
					+ ") (select (select "
					+ str1.toUniqString()
					+ " "
					+ str2.toUniqString()
					+ ") "
					+ x
					+ ")))",
				name);
		} else if (left instanceof TerminalForm) {
			String str = ((TerminalForm) left).getNodeText();
			for (int i = 0;
				i < SimplifyBinaryForm.JACK_CONSTANT_FCT.length;
				++i) {
				if (SimplifyBinaryForm.JACK_CONSTANT_FCT[i].equals(str)) {
					SimplifyTranslationResult r =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						r,
						"(" + str + " " + r.toUniqString() + ")");
				}
			}
		}
		// general case
		return appendSimplifyBinOp("select", indent);
	}

	private SimplifyTranslationResult appendSimplifyBinOp(
		String operator,
		int indent)
		throws LanguageException {
		SimplifyTranslationResult r1 =
			(SimplifyTranslationResult) left.toLang("Simplify", indent);
		SimplifyTranslationResult r2 =
			(SimplifyTranslationResult) right.toLang("Simplify", indent);
		return new SimplifyTranslationResult(
			r1,
			r2,
			"("
				+ operator
				+ " "
				+ r1.toUniqString()
				+ " "
				+ r2.toUniqString()
				+ ")");
	}

	/**
	 * Handle the equality operator and removes the unneeded bool().
	 */
	private SimplifyTranslationResult appendSimplifyEq(int indent)
		throws LanguageException {
		//		if (left.getNodeType() == B_BOOL) {
		//			UnaryForm l = (UnaryForm) left;
		//			SimplifyTranslationResult str =
		//				(SimplifyTranslationResult) l.getExp().toLang(
		//					"Simplify",
		//					indent);
		//			switch (right.getNodeType()) {
		//				case B_BOOL :
		//					{
		//						UnaryForm r = (UnaryForm) right;
		//						SimplifyTranslationResult str1 =
		//							(SimplifyTranslationResult) r.getExp().toLang(
		//								"Simplify",
		//								indent);
		//						return new SimplifyTranslationResult(
		//							str,
		//							str1,
		//							"(IFF "
		//								+ str.toUniqString()
		//								+ " "
		//								+ str1.toUniqString()
		//								+ ") ");
		//					}
		//				case Ja_LITERAL_false :
		//					return new SimplifyTranslationResult(
		//						str,
		//						"(NOT " + str.toUniqString() + ") ");
		//				case Ja_LITERAL_true :
		//					return str;
		//				default :
		//					throw new jml2b.exceptions.InternalError(
		//						"appendSimplifyEq: don't know how to handle :" + right);
		//			}
		//		} else {
		return appendSimplifyBinOp("EQ", indent);
		//		}
	}

	/**
	 * Converts in Simplify a <code>EQUALS_SUBSTRACTION_DOM</code> node
	 * @param subs The current substraction to apply to the dom of the
	 * restricted formula.
	 * @return the converted formula
	 **/
	private SimplifyTranslationResult equalsSubsDomToSimmplify(
		String x,
		int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_FUNCTION_EQUALS :
				{
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) getLeft().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) getRight().toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str2,
						str3,
						"(EQ (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ "))");
				}
			case EQUALS_ON_OLD_INSTANCES :
				{
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) getLeft().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) getRight().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str4 =
						in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult("instances"));
					return new SimplifyTranslationResult(
						str4,
						str2,
						str3,
						"(IMPLIES "
							+ str4.toUniqString()
							+ " (EQ (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ ")))");
				}
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					String y = SimplifyLanguage.newName();
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) getLeft().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) getRight().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str4 =
						in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult("instances"));
					return new SimplifyTranslationResult(
						str4,
						str2,
						str3,
						"(FORALL ("
							+ y
							+ ") (IMPLIES "
							+ str4.toUniqString()
							+ " (EQ (select (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") "
							+ y
							+ ") (select (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ ") "
							+ y
							+ "))))");
				}
			case B_SUBSTRACTION_DOM :
				SimplifyTranslationResult str1 =
					(SimplifyTranslationResult) left.toLang("Simplify", indent);
				SimplifyTranslationResult str2 =
					in(new SimplifyTranslationResult(x), str1);
				SimplifyTranslationResult str3;
				if (right instanceof BinaryForm)
					str3 =
						(
							new SimplifyBinaryForm(
								(BinaryForm) right)).equalsSubsDomToSimmplify(
							x,
							indent);
				else
					str3 =
						(
							new SimplifyTriaryForm(
								(TriaryForm) right)).equalsSubsDomToSimmplify(
							x,
							indent);

				return new SimplifyTranslationResult(
					str2,
					str3,
					"(IMPLIES (NOT "
						+ str2.toUniqString()
						+ ") "
						+ str3.toUniqString()
						+ ")");
			default :
				throw new InternalError(
					"BinaryForm.equalsSubsDomToB(String) bad node type: "
						+ right.getNodeType());
		}
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case EQUALS_ON_OLD_INSTANCES :
				{
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str4 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult("instances"));
					return new SimplifyTranslationResult(
						str4,
						str2,
						str3,
						"(FORALL ("
							+ x
							+ ") (IMPLIES "
							+ str4.toUniqString()
							+ " (EQ (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ "))))");
				}
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					String x = SimplifyLanguage.newName();
					String y = SimplifyLanguage.newName();
					SimplifyTranslationResult str4 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult("instances"));
					return new SimplifyTranslationResult(
						str4,
						str2,
						str3,
						"(FORALL ("
							+ x
							+ " "
							+ y
							+ ") (IMPLIES "
							+ str4.toUniqString()
							+ " (EQ (select (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") "
							+ y
							+ ") (select (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ ") "
							+ y
							+ "))))");
				}
			case Ja_DIFFERENT_OP :
				return appendSimplifyBinOp("NEQ", indent);
			case Ja_EQUALS_OP :
				if (left.getNodeType() == B_BOOL) {
					if (right.getNodeType() == B_BOOL) {
						SimplifyTranslationResult str1 =
							(SimplifyTranslationResult) ((UnaryForm) left)
								.getExp().toLang("Simplify", indent);
						SimplifyTranslationResult str2 =
							(SimplifyTranslationResult) ((UnaryForm) right)
								.getExp()
								.toLang(
								"Simplify",
								indent);
						return new SimplifyTranslationResult(
							str1, str2, "(IFF" + str1.toUniqString() + "  " + str2.toUniqString() + ")");
					} else if (right.getNodeType() == Ja_LITERAL_true) {
						return ((UnaryForm) left).getExp().toLang("Simplify", indent);
						
					} else if (right.getNodeType() == Ja_LITERAL_false) {
						SimplifyTranslationResult str1 = (SimplifyTranslationResult)((UnaryForm) left).getExp().toLang("Simplify", indent);
						return new SimplifyTranslationResult(str1, "(NOT (" + str1.toUniqString() + "))");
					}
				} else if (right.getNodeType() == B_BOOL
						&& left.getNodeType() == Ja_LITERAL_true)
					return ((UnaryForm) right).getExp().toLang("Simplify", indent);
				else 
				return appendSimplifyEq(indent);
			case Ja_AND_OP :
			case Jm_AND_THEN :
				{
					// write the and operator
					// append the left and right parts, supressing the 
					// additional and
					SimplifyTranslationResult str1 = appendSimplifyAnd(indent);
					return new SimplifyTranslationResult(
						str1,
						"(AND " + str1.toUniqString() + ")");
				}
			case Ja_OR_OP :
			case Jm_OR_ELSE :
				return appendSimplifyBinOp("OR", indent);
			case Ja_LE_OP :
				return appendSimplifyBinOp("<=", indent);
			case Ja_LESS_OP :
				return appendSimplifyBinOp("<", indent);
			case Ja_GE_OP :
				return appendSimplifyBinOp(">=", indent);
			case Ja_GREATER_OP :
				return appendSimplifyBinOp(">", indent);
			case Jm_IMPLICATION_OP :
				return appendSimplifyBinOp("IMPLIES", indent);
				case ALL_ARRAY_ELEMS: {
						String x = SimplifyLanguage.newName();
						String y = SimplifyLanguage.newName();
						String name = SimplifyLanguage.newName();
						SimplifyTranslationResult str1 =
							(SimplifyTranslationResult) left.toLang(
								"Simplify",
								indent);
						SimplifyTranslationResult str2 =
							(SimplifyTranslationResult) right.toLang(
								"Simplify",
								indent);
						SimplifyTranslationResult str4 =
							SimplifyBinaryForm.in(
								new SimplifyTranslationResult(x),
								new SimplifyTranslationResult(name));
						return new SimplifyTranslationResult(
							str1,
							"(FORALL ("
								+ x
								+ ") (IFF "
								+ str4.toUniqString()
								+ "(EXISTS ("
								+ y
								+ ") (AND "
								+"(<= 0 " + x + ")" +
								  "(< " + x + "(select |arraylength| " +  str2.toUniqString() + "))"
								+ " (EQ "
								+ x
								+ " (select "
								+ str1.toUniqString()
								+ " (select "
								+ str2.toUniqString()
							+ " "
								+ y
								+ ")))))))",
							name);	
				}
			case ARRAY_ACCESS :
				if (left.getNodeType() == B_APPLICATION
					&& ((BinaryForm) left).getLeft() instanceof ElementsForm) {
					SimplifyTranslationResult r1 =
						(SimplifyTranslationResult) ((BinaryForm) left).getLeft().toLang(
							"Simplify",
							indent);
						SimplifyTranslationResult r2 =
							(SimplifyTranslationResult) ((BinaryForm) left).getRight().toLang(
								"Simplify",
								indent);
					SimplifyTranslationResult r3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						r1,
						r2,
						r3,
						"( select ( select "
							+ r1.toUniqString()
							+ " "
							+ r2.toUniqString()
							+ ") "
							+ r3.toUniqString()
							+ ")");
				}
			case B_APPLICATION :
				return appendSimplifyBApplication(indent);
			case Ja_ADD_OP :
				return appendSimplifyBinOp("+", indent);
			case Ja_NEGATIVE_OP :
				return appendSimplifyBinOp("-", indent);
			case Ja_MUL_OP :
				return appendSimplifyBinOp("*", indent);
			case Ja_DIV_OP :
				return appendSimplifyBinOp("j_div", indent);
			case Ja_MOD :
				return appendSimplifyBinOp("j_mod", indent);
			case B_OVERRIDING :
				switch (right.getNodeType()) {
					case B_COUPLE :
						return appendSimplifyBinOp("store", indent);
					case CONSTANT_FUNCTION :
						{
							String name = SimplifyLanguage.newName();
							String x = SimplifyLanguage.newName();
							SimplifyTranslationResult str2 =
								(SimplifyTranslationResult) left.toLang(
									"Simplify",
									indent);
							SimplifyTranslationResult str3 =
								(SimplifyTranslationResult)
									((BinaryForm) right)
									.getLeft()
									.toLang(
									"Simplify",
									indent);
							SimplifyTranslationResult str4 =
								(SimplifyTranslationResult)
									((BinaryForm) right)
									.getRight()
									.toLang(
									"Simplify",
									indent);
							return new SimplifyTranslationResult(
								str2,
								str3,
								str4,
								"(FORALL ("
									+ x
									+ ")"
									+ "(IMPLIES (EQ ( "
									+ str3.toUniqString()
									+ " "
									+ x
									+ ") |@true|)"
									+ "(EQ (select "
									+ name
									+ " "
									+ x
									+ ") "
									+ str4.toUniqString()
									+ ")))",
								"(FORALL ("
									+ x
									+ ")"
									+ "(IMPLIES (NEQ ("
									+ str3.toUniqString()
									+ " "
									+ x
									+ ") |@true|)"
									+ "(EQ (select "
									+ name
									+ " "
									+ x
									+ ")"
									+ "(select "
									+ str2.toUniqString()
									+ " "
									+ x
									+ "))))",
								name);
						}
					case CONSTANT_FUNCTION_FUNCTION :
						{
							String name = SimplifyLanguage.newName();
							String x = SimplifyLanguage.newName();
							String y = SimplifyLanguage.newName();
							SimplifyTranslationResult str1 =
								(SimplifyTranslationResult) left.toLang(
									"Simplify",
									indent);
							SimplifyTranslationResult str2 =
								(SimplifyTranslationResult)
									((TriaryForm) right)
									.getF1()
									.toLang(
									"Simplify",
									indent);
							SimplifyTranslationResult str21 =
								SimplifyBinaryForm.in(
									new SimplifyTranslationResult(x),
									str2);
							SimplifyTranslationResult str3 =
								(SimplifyTranslationResult)
									((TriaryForm) right)
									.getLeft()
									.toLang(
									"Simplify",
									indent);
							SimplifyTranslationResult str31 =
								SimplifyBinaryForm.in(
									new SimplifyTranslationResult(y),
									str3);
							SimplifyTranslationResult str4 =
								(SimplifyTranslationResult)
									((TriaryForm) right)
									.getRight()
									.toLang(
									"Simplify",
									indent);
							return new SimplifyTranslationResult(
								str1,
								str21,
								str31,
								str4,
								"(FORALL ("
									+ x
									+ " "
									+ y
									+ ")"
									+ "(IMPLIES "
									+ str21.toUniqString()
									+ "(IMPLIES "
									+ str31.toUniqString()
									+ "(EQ (select (select"
									+ name
									+ " "
									+ x
									+ ") "
									+ y
									+ ") "
									+ str4.toUniqString()
									+ "))))",
								"(FORALL ("
									+ x
									+ " "
									+ y
									+ ")"
									+ "(IMPLIES "
									+ str21.toUniqString()
									+ "(IMPLIES (NOT "
									+ str31.toUniqString()
									+ ") (EQ (select (select"
									+ name
									+ " "
									+ x
									+ ") "
									+ y
									+ ") (select (select "
									+ str1.toUniqString()
									+ " "
									+ x
									+ ") "
									+ y
									+ ")))))",
								"(FORALL ("
									+ x
									+ " "
									+ y
									+ ")"
									+ "(IMPLIES (NOT "
									+ str21.toUniqString()
									+ ") (EQ (select (select"
									+ name
									+ " "
									+ x
									+ ") "
									+ y
									+ ") (select (select "
									+ str1.toUniqString()
									+ " "
									+ x
									+ ") "
									+ y
									+ "))))",
								name);
						}
					case B_OVERRIDING :
						String name = SimplifyLanguage.newName();
						SimplifyTranslationResult str1 =
							(SimplifyTranslationResult) left.toLang(
								"Simplify",
								indent);
						SimplifyTranslationResult str =
							(SimplifyTranslationResult) appendsimplifyOverriding(right,
								str1.toUniqString(),
								name,
								indent);
						return new SimplifyTranslationResult(str1, str, name);
					default :
						//TODO finir la traduction de B_OVERRIDING
						throw new jml2b.exceptions.InternalError(
							"SimmplifyBinaryForm.toLang: unhandled case: "
								+ toString[getNodeType()]);
				}
			case Jm_IS_SUBTYPE :
				return appendSimplifyBinOp("<:", indent);

			case LOCAL_VAR_DECL :
				case LOCAL_ELEMENTS_DECL:
				return new SimplifyTranslationResult("TRUE");

			case B_COUPLE :
				{
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str1,
						str2,
						str1.toUniqString() + " " + str2.toUniqString());
				}
				//			case LOCAL_VAR_DECL :
			case B_IN :
				return in(
					(SimplifyTranslationResult) left.toLang("Simplify", indent),
					(SimplifyTranslationResult) right.toLang(
						"Simplify",
						indent));
			case B_SUBSTRACTION_DOM :
				{
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						in(new SimplifyTranslationResult(x), str1);
					SimplifyTranslationResult str3;
					if (right instanceof BinaryForm)
						str3 =
							(
								new SimplifyBinaryForm(
									(
										BinaryForm) right))
											.equalsSubsDomToSimmplify(
								x,
								indent);
					else
						str3 =
							(
								new SimplifyTriaryForm(
									(
										TriaryForm) right))
											.equalsSubsDomToSimmplify(
								x,
								indent);

					return new SimplifyTranslationResult(
						str2,
						str3,
						"(FORALL ("
							+ x
							+ ") (IMPLIES (NOT "
							+ str2.toUniqString()
							+ ") "
							+ str3.toUniqString()
							+ "))");
				}
			case GUARDED_SET :
				if (right.getNodeType() == IFormToken.B_BTRUE
					|| (right.getNodeType() == Ja_EQUALS_OP
						&& ((BinaryForm) right).getLeft().getNodeType()
							== Ja_LITERAL_true
						&& ((BinaryForm) right).getRight().getNodeType()
							== Ja_LITERAL_true))
					return left.toLang("Simplify", indent);
				else {
					String name = SimplifyLanguage.newName();
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult(name));
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str2);
					SimplifyTranslationResult str4 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);

					return new SimplifyTranslationResult(
						str1,
						str3,
						str4,
						"(FORALL ("
							+ x
							+ ") (IFF "
							+ str1.toUniqString()
							+ "(AND "
							+ str3.toUniqString()
							+ " "
							+ str4.toUniqString()
							+ ")))",
						name);
				}
			case Ja_COMMA :
				{
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);

					return new SimplifyTranslationResult(
						str1,
						str2,
						str1.toUniqString() + " " + str2.toUniqString());
				}
			case B_INTERVAL :
				{
					String name = SimplifyLanguage.newName();
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult(name));
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);

					return new SimplifyTranslationResult(
						str2,
						str3,
						"(FORALL ("
							+ x
							+ ") (IFF "
							+ str1.toUniqString()
							+ "(AND (<= "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (<= "
							+ x
							+ " "
							+ str3.toUniqString()
							+ "))))",
						name);
				}
			case B_UNION :
				{
					String name = SimplifyLanguage.newName();
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult(name));
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str21 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str2);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str31 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str3);

					return new SimplifyTranslationResult(
						str21,
						str31,
						"(FORALL ("
							+ x
							+ ") (IFF "
							+ str1.toUniqString()
							+ "(OR "
							+ str21.toUniqString()
							+ " "
							+ str31.toUniqString()
							+ ")))",
						name);
				}
			case INTERSECTION_IS_NOT_EMPTY :
				{
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str11 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str1);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str21 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str2);

					return new SimplifyTranslationResult(
						str11,
						str21,
						"(EXISTS ("
							+ x
							+ ") (AND "
							+ str11.toUniqString()
							+ " "
							+ str21.toUniqString()
							+ ")))");
				}
			case B_SET_EQUALS :
				{
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str11 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str1);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str21 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str2);

					return new SimplifyTranslationResult(
						str11,
						str21,
						"(FORALL ("
							+ x
							+ ") (IFF "
							+ str11.toUniqString()
							+ " "
							+ str21.toUniqString()
							+ "))");
				}
			case B_FUNCTION_EQUALS :
				{
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str1,
						str2,
						"(FORALL ("
							+ x
							+ ") (EQ (select "
							+ str1.toUniqString()
							+ " "
							+ x
							+ " ) (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ")))");
				}
			default :
				throw new jml2b.exceptions.InternalError(
					"SimmplifyBinaryForm.toLang: unhandled case: "
						+ toString[getNodeType()]);
		}
	}

	/**
	 * @return
	 */
	private ITranslationResult appendsimplifyOverriding(
		Formula f,
		String prevName,
		String lastName,
		int indent)
		throws LanguageException {
		switch (f.getNodeType()) {
			case B_COUPLE :
				{
					SimplifyBinaryForm sbf =
						new SimplifyBinaryForm((BinaryForm) f);
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) sbf.getLeft().toLang(
							"Simplify",
							0);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) sbf.getRight().toLang(
							"Simplify",
							0);
					return new SimplifyTranslationResult(
						str1,
						str2,
						"(FORALL ("
							+ x
							+ ")"
							+ "(IMPLIES (EQ "
							+ str1.toUniqString()
							+ " "
							+ x
							+ ") (EQ (select "
							+ lastName
							+ " "
							+ x
							+ ") "
							+ str2.toUniqString()
							+ ")))",
						"(FORALL ("
							+ x
							+ ")"
							+ "(IMPLIES (NEQ ("
							+ str1.toUniqString()
							+ " "
							+ x
							+ ")"
							+ "(EQ (select "
							+ lastName
							+ " "
							+ x
							+ ")"
							+ "(select "
							+ prevName
							+ " "
							+ x
							+ "))))",
						lastName);
				}
			case CONSTANT_FUNCTION :
				{
					SimplifyBinaryForm sbf =
						new SimplifyBinaryForm((BinaryForm) f);
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) sbf.getLeft().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str4 =
						(SimplifyTranslationResult) sbf.getRight().toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str3,
						str4,
						"(FORALL ("
							+ x
							+ ")"
							+ "(IMPLIES (EQ ( "
							+ str3.toUniqString()
							+ " "
							+ x
							+ ") |@true|)"
							+ "(EQ (select "
							+ lastName
							+ " "
							+ x
							+ ") "
							+ str4.toUniqString()
							+ ")))",
						"(FORALL ("
							+ x
							+ ")"
							+ "(IMPLIES (NEQ ("
							+ str3.toUniqString()
							+ " "
							+ x
							+ ") |@true|)"
							+ "(EQ (select "
							+ lastName
							+ " "
							+ x
							+ ")"
							+ "(select "
							+ prevName
							+ " "
							+ x
							+ "))))",
						lastName);
				}
			case CONSTANT_FUNCTION_FUNCTION :
				{
					SimplifyTriaryForm stf =
						new SimplifyTriaryForm((TriaryForm) f);
					String x = SimplifyLanguage.newName();
					String y = SimplifyLanguage.newName();
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) stf.getF1().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str21 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							str2);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) stf.getLeft().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str31 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(y),
							str3);
					SimplifyTranslationResult str4 =
						(SimplifyTranslationResult) stf.getRight().toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str21,
						str31,
						str4,
						"(FORALL ("
							+ x
							+ " "
							+ y
							+ ")"
							+ "(IMPLIES "
							+ str21.toUniqString()
							+ "(IMPLIES "
							+ str31.toUniqString()
							+ "(EQ (select (select"
							+ lastName
							+ " "
							+ x
							+ ") "
							+ y
							+ ") "
							+ str4.toUniqString()
							+ "))))",
						"(FORALL ("
							+ x
							+ " "
							+ y
							+ ")"
							+ "(IMPLIES "
							+ str21.toUniqString()
							+ "(IMPLIES (NOT "
							+ str31.toUniqString()
							+ ") (EQ (select (select"
							+ lastName
							+ " "
							+ x
							+ ") "
							+ y
							+ ") (select (select "
							+ prevName
							+ " "
							+ x
							+ ") "
							+ y
							+ ")))))",
						"(FORALL ("
							+ x
							+ " "
							+ y
							+ ")"
							+ "(IMPLIES (NOT "
							+ str21.toUniqString()
							+ ") (EQ (select (select"
							+ lastName
							+ " "
							+ x
							+ ") "
							+ y
							+ ") (select (select "
							+ prevName
							+ " "
							+ x
							+ ") "
							+ y
							+ "))))",
						lastName);
				}
			case B_OVERRIDING :
				SimplifyBinaryForm sbf = new SimplifyBinaryForm((BinaryForm) f);

				String name = SimplifyLanguage.newName();

				SimplifyTranslationResult str1 =
					(SimplifyTranslationResult) new SimplifyBinaryForm(
						(BinaryForm) right).appendsimplifyOverriding(
						sbf.getLeft(),
						prevName,
						name,
						indent);
				SimplifyTranslationResult str2 =
					(SimplifyTranslationResult) new SimplifyBinaryForm(
						(BinaryForm) right).appendsimplifyOverriding(
						sbf.getRight(),
						name,
						lastName,
						indent);
				return new SimplifyTranslationResult(str1, str2);
			default :
				throw new jml2b.exceptions.InternalError(
					"SimmplifyBinaryForm.appendsimplifyOverriding: unhandled case: "
						+ toString[right.getNodeType()]);
		}
	}
}
