//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import jack.util.Logger;
import coqPlugin.CoqTranslationResult;
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
public class CoqQuantifiedForm extends QuantifiedForm
	implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public CoqQuantifiedForm(QuantifiedForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		QuantifiedVarForm v;
		String res = "(";
		CoqTranslationResult ctr =
			(CoqTranslationResult) body.toLang("Coq", indent);
		CoqTranslationResult ctr1 = null;
		switch (getNodeType()) {
			case Jm_FORALL :
				v = vars;
				while (v != null) {
					CoqTranslationResult ctr2 = new CoqTranslationResult(v);
					if (ctr1 == null)
						ctr1 = ctr2;
					else
						ctr1 =
							new CoqTranslationResult(ctr1, ctr2);
								//(ctr1.isVariableDecl() ? "" : (ctr1 + " -> ")) + ctr2);
					v = v.getNext();
				}
				res += (ctr1.isVariableDecl() ? ("forall " + ctr1 + ", ") : (ctr1 + " -> (*here*)"))
					+ ctr.getForAllDecl() + ")";
//				ctr.clearPropPart();
				if(-1 != res.indexOf("arraylength_1")) {
					Logger.get().println("gotcha");
				}
				break;
			case Jm_EXISTS :
				res = "";
				v = vars;
				while (v != null) {
					CoqTranslationResult tr = new CoqTranslationResult(v);
					String local = tr.getLocalDecl();
					if(local.indexOf("(") != -1) {
						local = local.replace('(', ' ');
						local = local.replace(')', ' ');
					}
					res += "(exists " + local + ", ";
					
					v = v.getNext();
				}
				res += ctr.getForAllDecl();
//				ctr.clearPropPart();
				for(v = vars; v != null; v = v.getNext()) {
					res += ")";
				}

				break;
			default :
				throw new InternalError(
					"CoqQuantifiedForm.toLang: unhandled case: "
						+ toString[getNodeType()]);
		}
		return new CoqTranslationResult(res);

	}
}
