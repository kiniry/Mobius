//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BDisplayedLanguage extends BLanguage {

//	public BDisplayedLanguage() {
//		Languages.register(
//			"BDisplayed",
//			this,
//			new BTranslationResult(),
//			new BPrinter());
//	}

	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new BBinaryForm("BDisplayed", (BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new BUnaryForm("BDisplayed", (UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new BQuantifiedForm("BDisplayed", (QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new BModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new BTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new BTriaryForm("BDisplayed", (TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new BTTypeForm("BDisplayed", (TTypeForm) f);

		return null;
	}

	public ITranslatable typeFactory(Type t) {
		return new BDisplayedType((Type) t);
	}

}
