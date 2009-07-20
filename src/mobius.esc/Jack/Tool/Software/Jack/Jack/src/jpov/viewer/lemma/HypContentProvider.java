//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: HypContentProvider.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.lemma;

import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.languages.Languages;
import jpov.structure.Lemma;
import jpov.structure.LemmaHierarchy;
import jpov.structure.VirtualFormula;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * @author L. Burdy, A. Requet
 **/
public class HypContentProvider implements IStructuredContentProvider {

	String language;

	HypContentProvider(String language) {
		this.language = language;
	}

	/**
	 * Converts a formula into the displayed language
	 * @param f The array of formulas to convert
	 * @return the string to display in the viewer
	 **/
	private String [] toLanguage(VirtualFormula [] f) {
		String [] tab; //= new String [f.length];
		try {
			tab = Languages.getLanguageClass(language).displayHyp(f);
			
			return tab;
		} catch (TranslationException te) {
			tab = new String[1];
			tab[0] = te.getMessage();
			return tab;
		} catch (LanguageException le) {
			throw new InternalError(le.getMessage());
		}
	}


	/**
	 * If the <code>inputElement</code> is a lemma, returns the array of hypline
	 * containing the hypothesis corresponding to this lemma
	 **/
	public final Object[] getElements(Object inputElement) {
		Object[] res;
		VirtualFormula [] vftab;
		if(inputElement == null)
			return new Object[0];
		if (inputElement instanceof Lemma) {
			Lemma l = (Lemma) inputElement;	
			vftab = l.getHyp();	
			
		} else if (inputElement instanceof LemmaHierarchy) {
			LemmaHierarchy l = (LemmaHierarchy) inputElement;
			Object []o = l.getHyp().toArray();
			vftab = new VirtualFormula[o.length];
			for(int i=0; i < vftab.length; i++) {
				vftab[i] =(VirtualFormula) o[i];
			}
		} else {
			return new Object[0];
		}
		
		String [] stab = toLanguage(vftab);	
		//Count the line numbers
		int count = 0;
		for (int i = 0; i < stab.length; i++)
			count += jml2b.util.Util.countTokens(stab[i], "\n");

		// create the array            
		res = new HypLine[count];
		count = 0;
		for (int i = 0; i < stab.length; i++) {
			// each hypothese is cut in line
			String[] s =
				jml2b.util.Util.tokenize(stab[i], "\n");
			// each line become an HypLine    
			for (int j = 0; j < s.length; j++)
				res[count++] = new HypLine(vftab[i], s[j], j == 0);
		}
		return res;
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

	public void dispose() {
	}
}
