//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyBinaryForm extends BinaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
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

	HarveyBinaryForm(BinaryForm f) {
		super(f);
	}

	static HarveyTranslationResult in(
		HarveyTranslationResult left,
		HarveyTranslationResult right) {
		return new HarveyTranslationResult(
			left,
			right,
			"(= ("
				+ right.toUniqString()
				+ " "
				+ left.toUniqString()
				+ ") tt)");
	}

	/**
	 * Converts the content of this AND node into simplify output, suppressing
	 * the unneeded ANDs (Simplify's and is nary and not binary).
	 */
	//@ requires nodeType.n() == B_AND_OP;
	private HarveyTranslationResult and(int indent) throws LanguageException {
		HarveyTranslationResult r1 = null;
		HarveyTranslationResult r2 = null;
		if (left.getNodeType() == Ja_AND_OP
			|| left.getNodeType() == Jm_AND_THEN) {
			HarveyBinaryForm bf = new HarveyBinaryForm((BinaryForm) left);
			r1 = bf.and(indent);
		} else {
			r1 = (HarveyTranslationResult) left.toLang("Harvey", indent);
		}
		if (right.getNodeType() == Ja_AND_OP
			|| right.getNodeType() == Jm_AND_THEN) {
			HarveyBinaryForm bf = new HarveyBinaryForm((BinaryForm) right);
			r2 = bf.and(indent);
		} else {
			r2 = (HarveyTranslationResult) right.toLang("Harvey", indent);
		}
		return new HarveyTranslationResult(
			r1,
			r2,
			r1.toUniqString() + " " + r2.toUniqString());
	}

	private HarveyTranslationResult application(int indent)
		throws LanguageException {
		// check if the left child is an identifier corresponding
		// to a known function
		if (left instanceof ElementsForm) {
			String x = HarveyLanguage.newName();
			String name = HarveyLanguage.newName();
			HarveyTranslationResult str1 =
				(HarveyTranslationResult) left.toLang("Harvey", indent);
			HarveyTranslationResult str2 =
				(HarveyTranslationResult) right.toLang("Harvey", indent);
			return new HarveyTranslationResult(
				str1,
				str2,
				"(forall "
					+ x
					+ " (= (select "
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
				i < HarveyBinaryForm.JACK_CONSTANT_FCT.length;
				++i) {
				if (HarveyBinaryForm.JACK_CONSTANT_FCT[i].equals(str)) {
					HarveyTranslationResult r =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						r,
						"(" + str + " " + r.toUniqString() + ")");
				}
			}
		}
		// general case
		return binOp("select", indent);
	}

	private HarveyTranslationResult binOp(String operator, int indent)
		throws LanguageException {
		HarveyTranslationResult r1 =
			(HarveyTranslationResult) left.toLang("Harvey", indent);
		HarveyTranslationResult r2 =
			(HarveyTranslationResult) right.toLang("Harvey", indent);
		return new HarveyTranslationResult(
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
	 * Converts in Simplify a <code>EQUALS_SUBSTRACTION_DOM</code> node
	 * @param subs The current substraction to apply to the dom of the
	 * restricted formula.
	 * @return the converted formula
	 **/
	private HarveyTranslationResult equalsSubsDomToSimmplify(
		String x,
		int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_FUNCTION_EQUALS :
				{
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) getLeft().toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) getRight().toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						str2,
						str3,
						"(= (select "
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
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) getLeft().toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) getRight().toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str4 =
						in(
							new HarveyTranslationResult(x),
							new HarveyTranslationResult("instances"));
					return new HarveyTranslationResult(
						str4,
						str2,
						str3,
						"(-> "
							+ str4.toUniqString()
							+ " (= (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ ")))");
				}
			case B_SUBSTRACTION_DOM :
				HarveyTranslationResult str1 =
					(HarveyTranslationResult) left.toLang("Harvey", indent);
				HarveyTranslationResult str2 =
					in(new HarveyTranslationResult(x), str1);

				HarveyTranslationResult str3;
				if (right instanceof BinaryForm)
					str3 =
						(
							new HarveyBinaryForm(
								(BinaryForm) right)).equalsSubsDomToSimmplify(
							x,
							indent);
				else
					str3 =
						(
							new HarveyTriaryForm(
								(TriaryForm) right)).equalsSubsDomToSimmplify(
							x,
							indent);

				return new HarveyTranslationResult(
					str2,
					str3,
					"(-> (not "
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
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str4 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							new HarveyTranslationResult("instances"));
					return new HarveyTranslationResult(
						str4,
						str2,
						str3,
						"(forall "
							+ x
							+ " (-> "
							+ str4.toUniqString()
							+ " (= (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ "))))");
				}
			case Ja_DIFFERENT_OP :
				{
					HarveyTranslationResult r1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult r2 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						r1,
						r2,
						"(not (= "
							+ r1.toUniqString()
							+ " "
							+ r2.toUniqString()
							+ "))");
				}
			case Ja_EQUALS_OP :
				return binOp("=", indent);
			case Ja_AND_OP :
			case Jm_AND_THEN :
				{
					// write the and operator
					// append the left and right parts, supressing the 
					// additional and
					HarveyTranslationResult str1 = and(indent);
					return new HarveyTranslationResult(
						str1,
						"(and " + str1.toUniqString() + ")");
				}
			case Ja_OR_OP :
			case Jm_OR_ELSE :
				return binOp("or", indent);
			case Ja_LE_OP :
				//				return binOp("<=", indent);
			case Ja_LESS_OP :
				//				return binOp("<", indent);
			case Ja_GE_OP :
				//				return binOp(">=", indent);
			case Ja_GREATER_OP :
				//				return binOp(">", indent);
				throw new TranslationException(
					"Harvey translator does not handle " + getNodeType());
			case Jm_IMPLICATION_OP :
				return binOp("->", indent);
			case B_APPLICATION :
			case ARRAY_ACCESS :
				return application(indent);
			case Ja_ADD_OP :
				//				return binOp("+", indent);
			case Ja_NEGATIVE_OP :
				//				return binOp("-", indent);
			case Ja_MUL_OP :
				//				return binOp("*", indent);
			case Ja_DIV_OP :
				//				return binOp("j_div", indent);
			case Ja_MOD :
				//				return binOp("j_mod", indent);
				throw new TranslationException(
					"Harvey translator does not handle " + getNodeType());
			case B_OVERRIDING :
				switch (right.getNodeType()) {
					case B_COUPLE :
						return binOp("store", indent);
					case CONSTANT_FUNCTION :
						{
							String name = HarveyLanguage.newName();
							String x = HarveyLanguage.newName();
							HarveyTranslationResult str2 =
								(HarveyTranslationResult) left.toLang(
									"Harvey",
									indent);
							HarveyTranslationResult str3 =
								(HarveyTranslationResult) ((BinaryForm) right)
									.getLeft()
									.toLang(
									"Harvey",
									indent);
							HarveyTranslationResult str4 =
								(HarveyTranslationResult) ((BinaryForm) right)
									.getRight()
									.toLang(
									"Harvey",
									indent);
							return new HarveyTranslationResult(
								str2,
								str3,
								str4,
								"(forall "
									+ x
									+ "(-> (= ( "
									+ str3.toUniqString()
									+ " "
									+ x
									+ ") tt)"
									+ "(= (select "
									+ name
									+ " "
									+ x
									+ ") "
									+ str4.toUniqString()
									+ ")))",
								"(forall "
									+ x
									+ "(-> (not (= ("
									+ str3.toUniqString()
									+ " "
									+ x
									+ ") tt))"
									+ "(= (select "
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
							String name = HarveyLanguage.newName();
							String x = HarveyLanguage.newName();
							String y = HarveyLanguage.newName();
							HarveyTranslationResult str1 =
								(HarveyTranslationResult) left.toLang(
									"Harvey",
									indent);
							HarveyTranslationResult str2 =
								(HarveyTranslationResult) ((TriaryForm) right)
									.getF1()
									.toLang(
									"Harvey",
									indent);
							HarveyTranslationResult str21 =
								HarveyBinaryForm.in(
									new HarveyTranslationResult(x),
									str2);
							HarveyTranslationResult str3 =
								(HarveyTranslationResult) ((TriaryForm) right)
									.getLeft()
									.toLang(
									"Harvey",
									indent);
							HarveyTranslationResult str31 =
								HarveyBinaryForm.in(
									new HarveyTranslationResult(y),
									str3);
							HarveyTranslationResult str4 =
								(HarveyTranslationResult) ((TriaryForm) right)
									.getRight()
									.toLang(
									"Harvey",
									indent);
							return new HarveyTranslationResult(
								str1,
								str21,
								str31,
								str4,
								"(forall "
									+ x
									+ " "
									+ y
									+ " (-> "
									+ str21.toUniqString()
									+ "(-> "
									+ str31.toUniqString()
									+ "(= (select (select"
									+ name
									+ " "
									+ x
									+ ") "
									+ y
									+ ") "
									+ str4.toUniqString()
									+ "))))",
								"(forall "
									+ x
									+ " "
									+ y
									+ " (-> "
									+ str21.toUniqString()
									+ "(-> (not "
									+ str31.toUniqString()
									+ ") (= (select (select"
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
								"(forall "
									+ x
									+ " "
									+ y
									+ " (-> (not "
									+ str21.toUniqString()
									+ ") (= (select (select"
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
						//TODO
					default :
						//TODO
				}
			case Jm_IS_SUBTYPE :
				return binOp("subtype", indent);

			case LOCAL_VAR_DECL :
			case LOCAL_ELEMENTS_DECL :
				return new HarveyTranslationResult("true");

			case B_COUPLE :
				{
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						str1,
						str2,
						str1.toUniqString() + " " + str2.toUniqString());
				}
				//			case LOCAL_VAR_DECL :
			case B_IN :
				return in(
					(HarveyTranslationResult) left.toLang("Harvey", indent),
					(HarveyTranslationResult) right.toLang("Harvey", indent));
			case B_SUBSTRACTION_DOM :
				{
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						in(new HarveyTranslationResult(x), str1);
					HarveyTranslationResult str3;
					if (right instanceof BinaryForm)
						str3 =
							(
								new HarveyBinaryForm(
									(
										BinaryForm) right))
											.equalsSubsDomToSimmplify(
								x,
								indent);
					else
						str3 =
							(
								new HarveyTriaryForm(
									(
										TriaryForm) right))
											.equalsSubsDomToSimmplify(
								x,
								indent);

					return new HarveyTranslationResult(
						str2,
						str3,
						"(forall "
							+ x
							+ " (-> (not "
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
					return left.toLang("Harvey", indent);
				else {
					String name = HarveyLanguage.newName();
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							new HarveyTranslationResult(name));
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str3 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str2);
					HarveyTranslationResult str4 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);

					return new HarveyTranslationResult(
						str1,
						str3,
						str4,
						"(forall "
							+ x
							+ " (<-> "
							+ str1.toUniqString()
							+ "(and "
							+ str3.toUniqString()
							+ " "
							+ str4.toUniqString()
							+ ")))",
						name);
				}
			case Ja_COMMA :
				{
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);

					return new HarveyTranslationResult(
						str1,
						str2,
						str1.toUniqString() + " " + str2.toUniqString());
				}
			case B_INTERVAL :
				//				{
				//					String name = HarveyLanguage.newName();
				//					String x = HarveyLanguage.newName();
				//					HarveyTranslationResult str1 =
				//						HarveyBinaryForm.in(
				//							new HarveyTranslationResult(x),
				//							new HarveyTranslationResult(name));
				//					HarveyTranslationResult str2 =
				//						(HarveyTranslationResult) left.toLang("Harvey", indent);
				//					HarveyTranslationResult str3 =
				//						(HarveyTranslationResult) right.toLang(
				//							"Harvey",
				//							indent);
				//
				//					return new HarveyTranslationResult(
				//						str2,
				//						str3,
				//						"(forall "
				//							+ x
				//							+ " (<-> "
				//							+ str1.toUniqString()
				//							+ "(and (<= "
				//							+ str2.toUniqString()
				//							+ " "
				//							+ x
				//							+ ") (<= "
				//							+ x
				//							+ " "
				//							+ str3.toUniqString()
				//							+ "))))",
				//						name);
				//				}
				throw new TranslationException(
					"Harvey translator does not handle " + getNodeType());

			case B_UNION :
				{
					String name = HarveyLanguage.newName();
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							new HarveyTranslationResult(name));
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str21 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str2);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str31 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str3);

					return new HarveyTranslationResult(
						str21,
						str31,
						"(forall "
							+ x
							+ " (<-> "
							+ str1.toUniqString()
							+ "(or "
							+ str21.toUniqString()
							+ " "
							+ str31.toUniqString()
							+ ")))",
						name);
				}
			case INTERSECTION_IS_NOT_EMPTY :
				{
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str11 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str1);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str21 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str2);

					return new HarveyTranslationResult(
						str11,
						str21,
						"(exists ("
							+ x
							+ ") (and "
							+ str11.toUniqString()
							+ " "
							+ str21.toUniqString()
							+ ")))");
				}
			case B_SET_EQUALS :
				{
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str11 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str1);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str21 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							str2);

					return new HarveyTranslationResult(
						str11,
						str21,
						"(forall "
							+ x
							+ " (<-> "
							+ str11.toUniqString()
							+ " "
							+ str21.toUniqString()
							+ "))");
				}
			case B_FUNCTION_EQUALS :
				{
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						str1,
						str2,
						"(forall "
							+ x
							+ " (= (select "
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
					"HarveyBinaryForm.toLang: unhandled case: "
						+ toString[getNodeType()]);
		}
	}
}
