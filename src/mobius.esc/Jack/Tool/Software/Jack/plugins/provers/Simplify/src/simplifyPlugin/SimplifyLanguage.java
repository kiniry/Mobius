//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import java.io.IOException;

import jml2b.exceptions.LanguageException;
import jml2b.formula.BinaryForm;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.Formula;
import jml2b.formula.MethodCallForm;
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
public class SimplifyLanguage extends ALanguage {

	static int nameCounter = 0;

	static String newName() {
		return "|@l" + nameCounter++ +"|";
	}

	public ITranslatable formulaFactory(Formula f) {
		if (f instanceof BinaryForm)
			return new SimplifyBinaryForm((BinaryForm) f);
		else if (f instanceof UnaryForm)
			return new SimplifyUnaryForm((UnaryForm) f);
		else if (f instanceof QuantifiedForm)
			return new SimplifyQuantifiedForm((QuantifiedForm) f);
		else if (f instanceof ModifiedFieldForm)
			return new SimplifyModifiedFieldForm((ModifiedFieldForm) f);
		else if (f instanceof TerminalForm)
			return new SimplifyTerminalForm((TerminalForm) f);
		else if (f instanceof TriaryForm)
			return new SimplifyTriaryForm((TriaryForm) f);
		else if (f instanceof TTypeForm)
			return new SimplifyTTypeForm((TTypeForm) f);
		else if (f instanceof DeclPureMethodForm) 
			return new SimplifyDeclPureMethodForm((DeclPureMethodForm)f);
		else if (f instanceof MethodCallForm)
			return new SimplifyMethodCallForm((MethodCallForm)f);
		return null;
	}

	public ITranslatable typeFactory(Type t) {
		return new SimplifyType((Type) t);
	}

	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf) {
		return new SimplifyQuantifiedVarForm(qvf);
	}

	public String displayGoal(Goal g, boolean applySubstitution) {
		try {
			String res = "";
			SimplifyTranslationResult str =
				(SimplifyTranslationResult) g.getVf().getF().toLang(
					"Simplify",
					0);
			String[] st = str.toStrings();
			for (int i = 0; i < st.length; i++)
				res += ("(IMPLIES " + st[i] + " ");
			res += (str.toUniqString());
			for (int i = 0; i < st.length; i++)
				res += ")";
			return res;
		} catch (LanguageException le) {
			return "Error: " + le.toString();
		} catch (jml2b.exceptions.InternalError e) {
			return "Error: " + e.toString();
		}
	}

	public void save(IOutputStream s, TerminalForm f)
		throws IOException, LanguageException {
		s.writeUTF(new SimplifyTerminalForm(f).toLang(0).toUniqString());
	}

	public void save(IOutputStream s, ITranslationResult result)
		throws IOException {
		s.writeUTF(result.toUniqString());
	}

	public ITranslationResult load(JpoInputStream s) throws IOException {
		return new SimplifyTranslationResult(s.readUTF());
	}

	public String getName() {
		return "Simplify";
	}

}
