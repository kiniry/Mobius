//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JmlFile
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.IOException;

import jml2b.exceptions.LoadException;
import jml2b.languages.Languages;
import jml2b.util.JpoInputStream;

/**
 * This class implements the root node of the tree.
 * @author L. Burdy
 **/
public class PartialJmlFile {

	private int nbPo;
	private int nbPoProved;
	private int[] poProved;

	/**
	 * Constructs a jml file from loaded informations
	 * @param fileName The associated file
	 * @param classes The array of classes
	 **/
	/*@
	  @ requires fileName != null && classes != null;
	  @*/
	public PartialJmlFile(JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {

		if (s.readInt()
			!= jml2b.structure.java.JmlFile.JPO_FILE_FORMAT_VERSION)
			throw new jml2b.exceptions.LoadException("Wrong file format.");
		s.readUTF();
		nbPo = s.readInt();
		nbPoProved = s.readInt();
		int nbLang = s.readInt(); // nbLanguages
		if (nbLang != Languages.getNbLanguages())
			throw new LoadException("Wrong file format");
		poProved = new int[nbLang];
		for (int i = 0; i < nbLang; i++) {
			if (Languages.getIndex(s.readUTF()) != i)
				throw new LoadException("Wrong file format");
			poProved[i] = s.readInt(); // nbPoProved
		}
	}

	/**
	 * @return
	 */
	public int getNbPo() {
		return nbPo;
	}

	/**
	 * @return
	 */
	public int getNbPoProved() {
		return nbPoProved;
	}

	/**
	 * @return
	 */
	public int getNbPOProved(String prover) {
		return poProved[Languages.getIndex(prover)];
	}

}
