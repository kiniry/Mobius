//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import coqPlugin.CoqLanguage;
import coqPlugin.CoqTranslationResult;
import jml2b.exceptions.LanguageException;
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqTriaryForm extends TriaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public CoqTriaryForm(TriaryForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		CoqTranslationResult ctr1 =
			(CoqTranslationResult) f1.toLang("Coq", indent);
		CoqTranslationResult ctr2 =
			(CoqTranslationResult) left.toLang("Coq", indent);
		CoqTranslationResult ctr3 =
			(CoqTranslationResult) right.toLang("Coq", indent);
		CoqTranslationResult res;
		String fun1 = ctr1.getFunPart();
		String fun2 = ctr2.getFunPart();
		String fun3 = ctr3.getFunPart();
		switch (getNodeType()) {
			case CONSTANT_FUNCTION_FUNCTION:
				return new CoqTranslationResult("(* Case Constant Fun Fun: you should not see me *) True");
			case B_ARRAY_EQUALS :
				return new CoqTranslationResult(
					ctr1, ctr2, ctr3,
					"(functionEquals "
						+ CoqType.basicType(
							left.getBasicType().getRtype().getLtype())
						+ " "
						+ CoqType.basicType(
							left.getBasicType().getRtype().getRtype())
						+ " (" + fun2 + " " + fun1 + ")" 
						+ " (" + fun3 + " " + fun1 + "))");

			case NEW_OBJECT :
				{
					String x = CoqLanguage.newName();
					
					return new CoqTranslationResult(
						ctr1, ctr2, ctr3,
						"forall " + x + ", "
							+ "("+ x + " <> " + fun1 + ") ->"
							+ "((" + fun2 + " " + x + ") =" + 
							  " (" + fun3 + " " + x + "))");
				}
			case ARRAY_RANGE :
				{
					String d = CoqLanguage.newName();
					String x = CoqLanguage.newName();
					String y = CoqLanguage.newName();
					String z = CoqLanguage.newName();
					CoqType t =
						CoqType.basicType(
							f1.getBasicType().getRtype().getRtype());
					ctr1.addPropPart(ctr2);
					ctr1.addPropPart(ctr3);
					String prop = ctr1.getPropPart();
					res = new CoqTranslationResult(
						ctr1, ctr2, ctr3, 
						"let " + d + ":" + t + " -> Prop := fun (" + x + ":" + t + ") => " +
								"(exists " + y + ", " +
										"(exists " + z + "," + (prop.equals("")? "" : prop + " -> ") +
												" (" + fun2 + " " + y + ") /\\ " +
												"(" + fun3 + " " + z + ") " +
												"/\\ (= " + t + " "	+ x + 
												"((" + fun1 + " " + y + ") " + z + ")))) in\n" + 
						d);
					res.clearPropPart();
					return res;
				}
			case Ja_QUESTION :
				{
					CoqType t = CoqType.basicType(left.getBasicType());
					return new CoqTranslationResult(
						ctr1,
						ctr2,
						ctr3,
						"(question " + t + " " + fun1 + " " + fun2 + " " + fun3 + ")");
				}
			default :
				throw new InternalError(
					"CoqTriaryForm.toLang: case not implemented: "
						+ toString[getNodeType()]);

		}

	}

	CoqTranslationResult equalsSubsDomToCoq(String x, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					CoqTranslationResult ctr1 =
						(CoqTranslationResult) getF1().toLang("Coq", indent);
					CoqTranslationResult ctr2 =
						(CoqTranslationResult) getLeft().toLang("Coq", indent);
					CoqTranslationResult ctr3 =
						(CoqTranslationResult) getRight().toLang("Coq", indent);
					String fun1 = ctr1.getFunPart();
					String fun2 = ctr2.getFunPart();
					String fun3 = ctr3.getFunPart();
					return new CoqTranslationResult(
						ctr1, ctr2, ctr3,
						"((" + fun2 + " " + fun1 + " " + x + ") =" +
						" (" + fun3 + " " + fun1 + " " + x + "))");
				}
			default :
				throw new InternalError(
					"CoqTriaryForm.equalsSubsDomToCoq(String) bad node type: "
						+ right.getNodeType());
		}
	}

}
