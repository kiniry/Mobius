//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.statement.Statement;

/**
 * @author L. Burdy
 */
public class JavaTriaryForm extends TriaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaTriaryForm(TriaryForm f) {
		super(f);
	}

	/**
	 * Converts the current formula to a string suitable for output into
	 * the Java view.
	 * @return 
	 * <UL> 
	 * <li> <code>cond ? left : right</code>
	 * <li> <code>left should not be modified</code>
	 * </UL>
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				return new JavaTranslationResult(
					f1.toLang("Java", indent).toUniqString()
						+ " == \\old("
						+ f1.toLang("Java", indent).toUniqString()
						+ ")",
					JavaLanguage.priority[Ja_EQUALS_OP]);
			case NEW_OBJECT :
				return new JavaTranslationResult(
					right.toLang("Java", indent).toUniqString()
						+ " is "
						+ left.toLang("Java", indent).toUniqString()
						+ " with a new instance "
						+ f1.toLang("Java", indent).toUniqString(),
					0);
			case ARRAY_RANGE :
				String x = Statement.fresh();
				return new JavaTranslationResult(
					"UNION("
						+ x
						+ ").("
						+ x
						+ ": "
						+ left.toLang("Java", indent).toUniqString()
						+ " | "
						+ f1.toLang("Java", indent).toUniqString()
						+ "("
						+ x
						+ ")["
						+ right.toLang("Java", indent).toUniqString()
						+ "])",
					0);
			case Ja_QUESTION :
				return new JavaTranslationResult(
					f1.toLangDefault(indent)
						+ " ? "
						+ left.toLangDefault(indent)
						+ " : "
						+ right.toLangDefault(indent),
					JavaLanguage.priority[getNodeType()]);
			case CONSTANT_FUNCTION_FUNCTION :
				return new JavaTranslationResult("", 0);
				//			case EQUAL_SUBSTRACTION_DOM :
				//				// return left.toJava(indent) + " == " + right.toJava(indent);
				//				return new JavaTranslationResult(
				//					left.toJava(indent) + " should not be modified");
			default :
				throw new InternalError(
					"JavaTriaryForm.toLang(int) bad node type:"
						+ getNodeType());
		}
	}

}
