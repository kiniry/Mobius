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
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsQuantifiedForm
	extends QuantifiedForm
	implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public PvsQuantifiedForm(QuantifiedForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = "";
		PvsTranslationResult ctr =
			(PvsTranslationResult) body.toLang("PVS", indent);
		PvsTranslationResult ctr1 = null;

		switch (getNodeType()) {
			case Jm_FORALL :
				res += "(FORALL ";
				break;
			case Jm_EXISTS :
				res += "(EXISTS ";
				break;
			default :
				throw new InternalError(
					"PvsQuantifiedForm.toLang: unhandled case: "
						+ toString[getNodeType()]);
		}

		QuantifiedVarForm v = vars;
		while (v != null) {
			PvsTranslationResult ctr2 = new PvsTranslationResult(v);
			if (ctr1 == null)
				ctr1 = ctr2;
			else
				ctr1 =
					new PvsTranslationResult(
						ctr1.toUniqString() + "," + ctr2.toUniqString());
			v = v.getNext();
		}

		res += ctr1.toUniqString() + ": " + ctr.toUniqString() + ")";

		return new PvsTranslationResult(res);
	}
}
