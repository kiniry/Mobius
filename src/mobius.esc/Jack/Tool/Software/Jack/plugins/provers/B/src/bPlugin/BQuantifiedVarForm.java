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

import jml2b.exceptions.LanguageException;
import jml2b.formula.QuantifiedVarForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BQuantifiedVarForm extends QuantifiedVarForm implements ITranslatable {

	BQuantifiedVarForm(QuantifiedVarForm qvf) {
		super(qvf);
		//		var = new BTerminalForm(qvf.getVar());
		//		type = Languages.getClass("B").formulaFactory(qvf.getType());
		//		if (qvf.getNext() != null)
		//			next = new BQuantifiedVarForm(qvf.getNext());
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = var.toLang("B", indent).toUniqString();
		QuantifiedVarForm tmp = next;
		while (tmp != null) {
			res += "," + tmp.getVar().toLang("B", indent).toUniqString();
			tmp = tmp.getNext();
		}
		res += ").(";
		res += var.toLang("B", indent).toUniqString()
			+ " : "
			+ type.toLang("B", indent).toUniqString();
		tmp = next;
		while (tmp != null) {
			res += " & "
				+ tmp.getVar().toLang("B", indent).toUniqString()
				+ " : "
				+ tmp.getType().toLang("B", indent).toUniqString();
			tmp = tmp.getNext();
		}
		return new BTranslationResult(res);
	}

	//	/**
	//	 * Converts the quantified variables into B variable list.
	//	 * @return the string corresponding to a B variable list comma separated.
	//	 **/
	//	String vartoB(int indent) throws LanguageException {
	//		String res = var.toLang("B", indent).toUniqString();
	//		if (next != null)
	//			res += "," + ((BQuantifiedVarForm) next).vartoB(indent);
	//		return res;
	//	}
	//
	//	/**
	//	 * Converts the quantified variables into B variable typing.
	//	 * @return the string corresponding to the B translation of the formula 
	//	 * typing
	//	 **/
	//	String typetoB(int indent) throws LanguageException {
	//		String res =
	//			var.toLang("B", indent).toUniqString()
	//				+ " : "
	//				+ type.toLang("B", indent).toUniqString();
	//		if (next != null)
	//			res += " & " + ((BQuantifiedVarForm) next).typetoB(indent);
	//		return res;
	//
	//	}

}
