//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * This class allows to translate a binary formula into the PVS language.
 * 
 * @author L. Burdy
 */
public class PvsBinaryForm extends BinaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public PvsBinaryForm(BinaryForm form) {
		super(form);
	}

	/**
	 * Returns the string in the PVS language corresponding to a token.
	 * @param n The token
	 * @param indent The current indentation value
	 * @return the B operator
	 * @throws InternalError when the token is unknown
	 **/
	public static String pvsConvert(int n, int indent) {
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
				return " OR ";
			case IFormToken.Ja_ADD_OP :
				return " + ";
			case IFormToken.Ja_NEGATIVE_OP :
				return " - ";
			case IFormToken.Ja_LE_OP :
				return " <= ";
			case IFormToken.Ja_LESS_OP :
				return " < ";
			case IFormToken.Ja_GE_OP :
				return " >= ";
			case IFormToken.Ja_GREATER_OP :
				return " > ";
			case IFormToken.Ja_MUL_OP :
				return " * ";
			case IFormToken.Ja_DIV_OP :
				return " / ";
			case Ja_COMMA :
				return ", ";
			case LOCAL_VAR_DECL :
				case LOCAL_ELEMENTS_DECL :
				return ":: ";
			default :
				throw new InternalError(
					"PvsBinaryForm.pvsConvert "
						+ n
						+ "("
						+ IFormToken.toString[n]
						+ ")");
		}
	}

	public PvsTranslationResult binOp(String op, int indent)
		throws LanguageException {
		PvsTranslationResult ctr1 =
			(PvsTranslationResult) left.toLang("PVS", indent);
		PvsTranslationResult ctr2 =
			(PvsTranslationResult) right.toLang("PVS", indent);
		return new PvsTranslationResult(
			op + "(" + ctr1.toUniqString() + "," + ctr2.toUniqString() + ")");

	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		PvsTranslationResult ctr1, ctr2;
		switch (getNodeType()) {
			case IS_MEMBER_FIELD :
				ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
				ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
				return new PvsTranslationResult(
					ctr1,
					ctr2,
					"["
						+ ctr1.toUniqString()
						+ " -> "
						+ ctr2.toUniqString()
						+ "]");

			case Ja_EQUALS_OP :
				if (left.getNodeType() == B_BOOL) {
					if (right.getNodeType() == B_BOOL) {
						ctr1 =
							(PvsTranslationResult) ((UnaryForm) left)
								.getExp()
								.toLang(
								"PVS",
								indent);
						ctr2 =
							(PvsTranslationResult) ((UnaryForm) right)
								.getExp()
								.toLang(
								"PVS",
								indent);
						return new PvsTranslationResult(
							ctr1,
							ctr2,
							ctr1.toUniqString()
								+ " <=> "
								+ ctr2.toUniqString());
					} else if (right.getNodeType() == Ja_LITERAL_true)
						return ((UnaryForm) left).getExp().toLang(
							"PVS",
							indent);
				} else if (
					right.getNodeType() == B_BOOL
						&& left.getNodeType() == Ja_LITERAL_true)
					return ((UnaryForm) right).getExp().toLang("PVS", indent);
				//end of special treatment of bool
			case Ja_COMMA :
			case Ja_LE_OP :
			case Ja_LESS_OP :
			case Ja_GE_OP :
			case Ja_GREATER_OP :
			case Ja_ADD_OP :
			case Ja_NEGATIVE_OP :
			case Ja_MUL_OP :
			case Ja_DIV_OP :
			case B_FUNCTION_EQUALS :
			case Jm_IMPLICATION_OP :
			case Ja_OR_OP :
			case Jm_OR_ELSE :
			case Ja_AND_OP :
			case Jm_AND_THEN :
			case Ja_DIFFERENT_OP :
				ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
				ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
				String res = "";
				if (PvsLanguage.priority[left.getNodeType()]
					< PvsLanguage.priority[getNodeType()]) {
					res = "(" + ctr1.toUniqString() + ")";
				} else
					res = ctr1.toUniqString();

				res += pvsConvert(getNodeType(), indent);

				if (right != null) {
					if (PvsLanguage.priority[right.getNodeType()]
						<= PvsLanguage.priority[getNodeType()]) {
						res += "(" + ctr2.toUniqString() + ")";
					} else
						res += ctr2.toUniqString();
				}
				return new PvsTranslationResult(ctr1, ctr2, res);
			case Ja_MOD :
				return binOp("j_rem", indent);
			case Jm_IS_SUBTYPE :
				return binOp("subtype", indent);
			case B_IN :
				ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
				ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
				return new PvsTranslationResult(
					ctr2.toUniqString() + "(" + ctr1.toUniqString() + ")");
			case ALL_ARRAY_ELEMS : {
					String x = PvsLanguage.newName();
					String y = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(LAMBDA ("
							+ x
							+ ":"
							+ PvsLanguage.basicType(
								left.getBasicType().getRtype())
							+ "): (EXISTS ("
							+ y
							+ ": t_int ): 0 <= "
							+ y
							+ " AND "
							+ y
							+ " < arraylength("
							+ ctr2.toUniqString()
							+ ") AND "
							+ ctr1.toUniqString()
							+ "("
							+ ctr2.toUniqString()
							+ "("
							+ y
							+ ")) = "
							+ x
							+ "))");
		}
			case B_APPLICATION :
			case ARRAY_ACCESS :
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
				return new PvsTranslationResult(
					ctr1.toUniqString() + "(" + ctr2.toUniqString() + ")");
			case LOCAL_VAR_DECL :
				case LOCAL_ELEMENTS_DECL :
				return new PvsTranslationResult(this);

			case B_UNION :
				{
					String x = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(LAMBDA ("
							+ x
							+ ":"
							+ PvsLanguage.basicType(
								left.getBasicType().getLtype())
							+ "): "
							+ ctr1.toUniqString()
							+ "("
							+ x
							+ ") OR "
							+ ctr2.toUniqString()
							+ "("
							+ x
							+ "))");
				}
			case B_COUPLE :
				{
					String x = PvsLanguage.newName();
					String y = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(LAMBDA ("
							+ x
							+ ":{"
							+ y
							+ ":"
							+ PvsLanguage.basicType(left.getBasicType())
							+ " | "
							+ y
							+ "="
							+ ctr1.toUniqString()
							+ "}): "
							+ ctr2.toUniqString()
							+ ")");
				}
			case B_INTERVAL :
				ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
				ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
				return new PvsTranslationResult(
					ctr1,
					ctr2,
					"(LAMBDA (x:integer): "
						+ ctr1.toUniqString()
						+ " <= x AND x <= "
						+ ctr2.toUniqString()
						+ ")");
			case INTERSECTION_IS_NOT_EMPTY :
				{
					String x = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(EXISTS ("
							+ x
							+ ":"
							+ PvsLanguage.basicType(
								left.getBasicType().getLtype())
							+ ") : "
							+ ctr1.toUniqString()
							+ "("
							+ x
							+ ") AND "
							+ ctr2.toUniqString()
							+ "("
							+ x
							+ "))");
				}
			case B_SET_EQUALS :
				{
					String x = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(FORALL ("
							+ x
							+ ": "
							+ PvsLanguage.basicType(
								left.getBasicType().getLtype())
							+ "): "
							+ ctr1.toUniqString()
							+ "("
							+ x
							+ ") = "
							+ ctr2.toUniqString()
							+ "("
							+ x
							+ "))");
				}
			case B_OVERRIDING :
				switch (right.getNodeType()) {
					case B_COUPLE :
						{
							ctr1 =
								(PvsTranslationResult) left.toLang(
									"PVS",
									indent);
							ctr2 =
								(PvsTranslationResult) ((BinaryForm) right)
									.getLeft()
									.toLang(
									"PVS",
									indent);
							PvsTranslationResult ctr3 =
								(PvsTranslationResult) ((BinaryForm) right)
									.getRight()
									.toLang(
									"PVS",
									indent);
							return new PvsTranslationResult(
								ctr1,
								ctr2,
								ctr3,
								ctr1.toUniqString()
									+ " WITH [("
									+ ctr2.toUniqString()
									+ ") := "
									+ ctr3.toUniqString()
									+ "]");
						}
					case CONSTANT_FUNCTION :
						{
							String x = PvsLanguage.newName();
							ctr1 =
								(PvsTranslationResult) left.toLang(
									"PVS",
									indent);
							ctr2 =
								(PvsTranslationResult) ((BinaryForm) right)
									.getLeft()
									.toLang(
									"PVS",
									indent);
							PvsTranslationResult ctr3 =
								(PvsTranslationResult) ((BinaryForm) right)
									.getRight()
									.toLang(
									"PVS",
									indent);
							return new PvsTranslationResult(
								ctr1,
								ctr2,
								ctr3,
								"(LAMBDA ("
									+ x
									+ ": "
									+ PvsLanguage.basicType(
										left.getBasicType().getLtype())
									+ "): IF "
									+ ctr2.toUniqString()
									+ "("
									+ x
									+ ") THEN "
									+ ctr3.toUniqString()
									+ " ELSE "
									+ ctr1.toUniqString()
									+ "("
									+ x
									+ ") ENDIF)");
						}
					case CONSTANT_FUNCTION_FUNCTION :
						{
							String x = PvsLanguage.newName();
							String y = PvsLanguage.newName();
							ctr1 =
								(PvsTranslationResult) left.toLang(
									"PVS",
									indent);
							ctr2 =
								(PvsTranslationResult) ((TriaryForm) right)
									.getF1()
									.toLang(
									"PVS",
									indent);
							PvsTranslationResult ctr3 =
								(PvsTranslationResult) ((TriaryForm) right)
									.getLeft()
									.toLang(
									"PVS",
									indent);
							PvsTranslationResult ctr4 =
								(PvsTranslationResult) ((TriaryForm) right)
									.getRight()
									.toLang(
									"PVS",
									indent);
							return new PvsTranslationResult(
								ctr1,
								ctr2,
								ctr3,
								ctr4,
								"(LAMBDA ("
									+ x
									+ ": "
									+ PvsLanguage.basicType(
										left.getBasicType().getLtype())
									+ "): IF "
									+ ctr2.toUniqString()
									+ "("
									+ x
									+ ") THEN (LAMBDA ("
									+ y
									+ ": "
									+ PvsLanguage.basicType(
										left
											.getBasicType()
											.getRtype()
											.getLtype())
									+ "): IF "
									+ ctr3.toUniqString()
									+ "("
									+ y
									+ ") THEN "
									+ ctr4.toUniqString()
									+ " ELSE "
									+ ctr1.toUniqString()
									+ "("
									+ x
									+ ")("
									+ y
									+ ") ENDIF) ELSE "
									+ ctr1.toUniqString()
									+ "("
									+ x
									+ ") ENDIF)");
						}
					case B_OVERRIDING :
						//TODO Finir de traduire B_OVERRIDING
					default :
						throw new jml2b.exceptions.InternalError(
							"pVSBinaryForm.toLang: unhandled case: "
								+ toString[getNodeType()]);
				}
			case EQUALS_ON_OLD_INSTANCES :
				{
					String n = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(FORALL ("
							+ n
							+ ":REFERENCES): instances?("
							+ n
							+ ") => "
							+ ctr1.toUniqString()
							+ "("
							+ n
							+ ") = "
							+ ctr2.toUniqString()
							+ "("
							+ n
							+ "))");
				}
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					String x = PvsLanguage.newName();
					String y = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(FORALL ("
							+ x
							+ ":REFERENCES) ("
							+ y
							+ ":integer): instances?("
							+ x
							+ ") => "
							+ ctr1.toUniqString()
							+ "("
							+ x
							+ ")("
							+ y
							+ ") = "
							+ ctr2.toUniqString()
							+ "("
							+ x
							+ ")("
							+ y
							+ "))");
				}
			case B_SUBSTRACTION_DOM :
				{
					String x = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					if (right instanceof BinaryForm)
						ctr2 =
							(
								new PvsBinaryForm(
									(BinaryForm) right)).equalsSubsDomToPvs(
								x,
								indent);
					else
						ctr2 =
							(
								new PvsTriaryForm(
									(TriaryForm) right)).equalsSubsDomToPvs(
								x,
								indent);

					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(FORALL ("
							+ x
							+ ":"
							+ PvsLanguage.basicType(
								left.getBasicType().getLtype())
							+ "): NOT ("
							+ ctr1.toUniqString()
							+ "("
							+ x
							+ ")) => "
							+ ctr2.toUniqString()
							+ ")");
				}
			case GUARDED_SET :
				if (right.getNodeType() == IFormToken.B_BTRUE
					|| (right.getNodeType() == Ja_EQUALS_OP
						&& ((BinaryForm) right).getLeft().getNodeType()
							== Ja_LITERAL_true
						&& ((BinaryForm) right).getRight().getNodeType()
							== Ja_LITERAL_true))
					return left.toLang("PVS", indent);
				else {
					String x = PvsLanguage.newName();
					ctr1 = (PvsTranslationResult) left.toLang("PVS", indent);
					ctr2 = (PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						"(LAMBDA ("
							+ x
							+ ": "
							+ PvsLanguage.basicType(
								left.getBasicType().getLtype())
							+ "): "
							+ ctr1.toUniqString()
							+ "("
							+ x
							+ ") AND "
							+ ctr2.toUniqString()
							+ ")");
				}
			default :
				throw new TranslationException(
					"pVSBinaryForm.toLang: unhandled case: "
						+ toString[getNodeType()]);
		}
	}

	private PvsTranslationResult equalsSubsDomToPvs(String x, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_FUNCTION_EQUALS :
				{
					PvsTranslationResult ctr2 =
						(PvsTranslationResult) getLeft().toLang("PVS", indent);
					PvsTranslationResult ctr3 =
						(PvsTranslationResult) getRight().toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr2,
						ctr3,
						ctr2.toUniqString()
							+ "("
							+ x
							+ ") = "
							+ ctr3.toUniqString()
							+ "("
							+ x
							+ ")");
				}
			case EQUALS_ON_OLD_INSTANCES :
				{
					PvsTranslationResult ctr2 =
						(PvsTranslationResult) getLeft().toLang("PVS", indent);
					PvsTranslationResult ctr3 =
						(PvsTranslationResult) getRight().toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr2,
						ctr3,
						"instances?("
							+ x
							+ ") => "
							+ ctr2.toUniqString()
							+ "("
							+ x
							+ ") = "
							+ ctr3.toUniqString()
							+ "("
							+ x
							+ ")");
				}
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				{
					String y = PvsLanguage.newName();
					PvsTranslationResult ctr2 =
						(PvsTranslationResult) getLeft().toLang("PVS", indent);
					PvsTranslationResult ctr3 =
						(PvsTranslationResult) getRight().toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr2,
						ctr3,
						"(FORALL ("
							+ y
							+ ": "
							+ PvsLanguage.basicType(
								left.getBasicType().getRtype().getLtype())
							+ "): instances?("
							+ x
							+ ") =>"
							+ ctr2.toUniqString()
							+ "("
							+ x
							+ ")("
							+ y
							+ ") = "
							+ ctr3.toUniqString()
							+ "("
							+ x
							+ ")("
							+ y
							+ "))");
				}
			case B_SUBSTRACTION_DOM :
				PvsTranslationResult ctr1 =
					(PvsTranslationResult) left.toLang("PVS", indent);

				PvsTranslationResult ctr3;
				if (right instanceof BinaryForm)
					ctr3 =
						(
							new PvsBinaryForm(
								(BinaryForm) right)).equalsSubsDomToPvs(
							x,
							indent);
				else
					ctr3 =
						(
							new PvsTriaryForm(
								(TriaryForm) right)).equalsSubsDomToPvs(
							x,
							indent);

				return new PvsTranslationResult(
					ctr1,
					ctr3,
					"NOT ("
						+ ctr1.toUniqString()
						+ "("
						+ x
						+ ")) =>"
						+ ctr3.toUniqString());
			default :
				throw new InternalError(
					"PvsBinaryForm.equalsSubsDomToPvs(String) bad node type: "
						+ right.getNodeType());
		}
	}

}
