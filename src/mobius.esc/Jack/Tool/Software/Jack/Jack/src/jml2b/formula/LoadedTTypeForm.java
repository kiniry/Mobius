//******************************************************************************
//* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: LoadedTTypeForm.java
//*
//*******************************************************************************
//* Warnings/Remarks:
//******************************************************************************/

package jml2b.formula;

import java.io.IOException;
import java.util.Hashtable;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.LoadException;
import jml2b.languages.ITranslationResult;
import jml2b.languages.Languages;
import jml2b.structure.java.IJmlFile;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;

/**
 * @author L. Burdy
 **/
final class LoadedTTypeForm extends TTypeForm {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private Hashtable languagesText = new Hashtable();

	private int tag;

	/**
	 * Constructs a formula from a loaded jpo file.
	 * @param nodeType The loaded node type, should be Jm_T_TYPE
	 * @param nodeText The loaded string
	 * @param s input stream corresponding to a jpo file. 
	 * @throws IOException if the end of the stream is reached before the 
	 * formula has been read
	 * @throws LoadException if the stream has not a good format.
	 **/
	public LoadedTTypeForm(IJml2bConfiguration config,
		IJmlFile fi,
		byte nodeType,
		String nodeText,
		JpoInputStream s)
		throws IOException {
		//@ set comesFromLoad = true;
		super(nodeType, null);
		this.nodeText = nodeText;
		tag = s.readInt();
		bNative = s.readBoolean();
		int nbLang = fi.getLangNames().length;
		for (int i = 0; i < nbLang; i++) {
			//			String lang = s.readUTF();
			String text = s.readUTF();
			languagesText.put(fi.getLangNames()[i], text);
		}
		

	}

	public ITranslationResult toLang(String language, int indent)
		throws LanguageException {
		return Languages.getTranslationResultClass(language).Factory(
			(String) languagesText.get(language));
	}

	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
//		byte nb = (byte) languagesText.size();
		s.writeByte(getNodeType());
		s.writeUTF(nodeText);
		s.writeInt(tag);
		s.writeBoolean(bNative);
		for (int i = 0; i < jf.getLangNames().length; i++) {
			String lang = jf.getLangNames()[i];
				s.writeUTF((String) languagesText.get(lang));
		}
	}
	
	public int getTag() {
		return tag;
	}


}
