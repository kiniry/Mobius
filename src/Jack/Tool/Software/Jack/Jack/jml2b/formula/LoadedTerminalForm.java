//******************************************************************************
//* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: 
//*
//*******************************************************************************
//* Warnings/Remarks:
//******************************************************************************/

package jml2b.formula;

import java.io.IOException;
import java.util.Hashtable;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.languages.ITranslationResult;
import jml2b.languages.Languages;
import jml2b.languages.java.JavaTranslationResult;
import jml2b.structure.java.IJmlFile;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;

/**
 * @author L. Burdy
 **/
final class LoadedTerminalForm extends TerminalForm {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	Hashtable languagesText = new Hashtable();

	private BasicType bt;

	/**
	 * Constructs a formula from a loaded jpo file.
	 * @param nodeType The node type of this formula
	 * @param nodeText The string corresponding to this formula
	 * @param s input stream corresponding to a jpo file. 
	 * @throws IOException if the end of the stream is reached before the 
	 * formula has been read
	 * @throws LoadException if the stream has not a good format.
	 **/
	public LoadedTerminalForm(
		IJmlFile fi,
		byte nodeType,
		String nodeText,
		BasicType bt,
		JpoInputStream s)
		throws IOException {
		super(nodeType, nodeText, null, false);
		this.bt = bt;
		int nbLang = fi.getLangNames().length;
		for (int i = 0; i < nbLang; i++) {
			try {
				languagesText.put(
					fi.getLangNames()[i],
					Languages.getLanguageClass(fi.getLangNames()[i]).load(s));
			} catch (LanguageException le) {
				throw new InternalError(le.getMessage());
			}
		}
	}

	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
//		byte nb = (byte) languagesText.size();
		s.writeByte(getNodeType());
		s.writeUTF(getNodeText());
		bt.save(s);
		for (int i = 0; i < jf.getLangNames().length; i++) {
			try {
				String lang = jf.getLangNames()[i];
				Languages.getLanguageClass(lang).save(
					s,
					(ITranslationResult) languagesText.get(lang));

			} catch (LanguageException le) {
				throw new InternalError(le.getMessage());
			}
		}
	}

	public ITranslationResult toLang(String language, int indent)
		throws LanguageException {
		return (ITranslationResult) languagesText.get(language);
	}

	public int contains(Vector selectedFields) {
		String j =
			((JavaTranslationResult) languagesText.get("Java")).toUniqString();
		int p = j.indexOf("(");
		if (selectedFields.contains(j)
			|| (p != -1 && selectedFields.contains(j.substring(0, p))))
			return 1;
		else
			return 0;
	}
	
	public BasicType getBasicType() {
		return bt;
	}

}
