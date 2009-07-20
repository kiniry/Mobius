//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

import java.io.IOException;

import jml2b.exceptions.LanguageException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ALanguage;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;
import jpov.structure.Goal;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyLanguage extends ALanguage {

	static int nameCounter = 0;

	static String newName() {
		return "at_" + nameCounter++;
	}

	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new HarveyBinaryForm((BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new HarveyUnaryForm((UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new HarveyQuantifiedForm((QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new HarveyModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new HarveyTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new HarveyTriaryForm((TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new HarveyTTypeForm((TTypeForm) f);

		return null;
	}

	public ITranslatable typeFactory(Type t) {
		return new HarveyType((Type) t);
	}

	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf) {
		return new HarveyQuantifiedVarForm(qvf);
	}

	public String displayGoal(Goal g, boolean applySubstitution) {
		try {
			String res = "Local declarations";
			HarveyTranslationResult str =
				(HarveyTranslationResult) g.getVf().getF().toLang("Harvey", 0);
			String[] st = str.toStrings();
			for (int i = 0; i < st.length; i++)
				res += "\n" + st[i];
			res += "\nGoal\n" + str.toUniqString();
			return res;
		} catch (LanguageException le) {
			return "Error: " + le.toString();
		} catch (jml2b.exceptions.InternalError e) {
			return "Error: " + e.toString();
		}
	}

	public void save(IOutputStream s, TerminalForm f)
		throws IOException, LanguageException {
		s.writeUTF(new HarveyTerminalForm(f).toLang(0).toUniqString());
	}

	public void save(IOutputStream s, ITranslationResult result)
		throws IOException {
		s.writeUTF(result.toUniqString());
	}

	public ITranslationResult load(JpoInputStream s) throws IOException {
		return new HarveyTranslationResult(s.readUTF());
	}



	public String getName() {
		return "Harvey";
	}

}
