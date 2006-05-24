//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Method
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.IOException;
import java.util.ArrayList;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LoadException;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class implements a node tree corresponding to a method.
 * @author L. Burdy
 **/
public class Method extends TreeObject {

	/**
	 * Loads a method from a
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the jpo file
	 * @return The constructed method.
	 **/
	static Method loadMethod(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		Method m = new Method(config, fi, s);
		//m.lemmas.setParent(m);
		m.wellDefinednessLemmas.setParent(m);
		return m;
	}

	/**
	 * The method name
	 **/
	private String name;

	/**
	 * The signature
	 **/
	private String signature;

	/**
	 * The method pmi name
	 **/
	private String pmiName;

	/**
	 * The first line of the method into the source text
	 **/
	private int firstLine;

	/**
	 * The cases associated to the method
	 **/
	private Proofs lemmas;

	private long lemmasFileIndex;
	private JpoInputStream jis;
	private IJml2bConfiguration config;
	private IJmlFile ijf;

	private Proofs wellDefinednessLemmas;

	private boolean isConstructor;

	private boolean isStatic;

	private int nbPo = -1;

	private int nbPoProved = -1;

	private int nbPoChecked;

	/*@
	  @ private invariant name != null
	  @                && signature != null
	  @                && pmiName != null
	  @                && lemmas != null;
	  @*/

	/**
	 * Constructs a method from a loaded
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the JPO file
	 **/
	public Method(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		name = s.readUTF();
		isConstructor = s.readBoolean();
		isStatic = s.readBoolean();
		signature = s.readUTF();
		pmiName = s.readUTF();
		firstLine = s.readInt();
		nbPo = s.readInt();
		nbPoProved = s.readInt();
		nbPoChecked = s.readInt();
		lemmasFileIndex = s.getFilePointer();
		jis = s;
		this.config = config;
		ijf = fi;
		new Proofs(config, fi, s);
		wellDefinednessLemmas = new WellDefinedMethodProofs(config, fi, s);
	}

	/**
	 * @return the name plus the signature of the method
	 **/
	public String getText(int type) {
		return name + signature;
	}

	public int getNbPo() {
		if (nbPo == -1)
			return nbPo =
				getLemmas().getNbPo() + wellDefinednessLemmas.getNbPo();
		else
			return nbPo;
	}

	public int getNbPoProved() {
		if (nbPoProved == -1)
			return nbPoProved =
				getLemmas().getNbPoProved()
					+ wellDefinednessLemmas.getNbPoProved();
		else
			return nbPoProved;
	}

	public int getNbPoProved(String prover) {
		return getLemmas().getNbPoProved(prover)
			+ wellDefinednessLemmas.getNbPoProved(prover);
	}

	public int getNbCheckedPo() {
		return nbPoChecked;
	}
	/**
	 * Returns the method pmi name
	 * @return <code>pmiName</code>
	 **/
	public String getPmiName() {
		return pmiName;
	}

	public void setChecked() {
		getLemmas().setChecked();
		wellDefinednessLemmas.setChecked();
	}

	public void setUnchecked() {
		getLemmas().setUnchecked();
		wellDefinednessLemmas.setUnchecked();
	}

	/**
	 * Saves the method into a
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The ouput stream corresponding to the jpo file
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeUTF(name);
		s.writeBoolean(isConstructor);
		s.writeBoolean(isStatic);
		s.writeUTF(signature);
		s.writeUTF(pmiName);
		s.writeInt(firstLine);
		s.writeInt(nbPo);
		s.writeInt(nbPoProved);
		s.writeInt(nbPoChecked);
		getLemmas().save(config, s, jf);
		wellDefinednessLemmas.save(config, s, jf);
	}

	/**
	 * Sets all the goals of this method to unprove.
	 **/
	void unprove() {
		getLemmas().unprove();
		wellDefinednessLemmas.unprove();
	}

	/**
	 * Returns the firstLine.
	 * @return <code>firstLine</code>
	 */
	public int getFirstLine() {
		return firstLine;
	}

	/**
	 * Returns the lemmas.
	 * @return <code>lemmas</code>
	 */
	public Proofs getLemmas() {
		if (lemmas == null) {
			try {
				jis.seek(lemmasFileIndex);
				lemmas = new Proofs(config, ijf, jis);
				lemmas.setParent(this);
			} catch (IOException ioe) {
				throw new jml2b.exceptions.InternalError(
					"JopInputStream.seek(): " + ioe.getMessage());
			} catch (LoadException ioe) {
				throw new jml2b.exceptions.InternalError(
					"JopInputStream.seek(): " + ioe.getMessage());
			}
		}
		return lemmas;
	}

	public Proofs getWellDefinednessLemmas() {
		return wellDefinednessLemmas;
	}

	/**
	 * @return
	 */
	public boolean isConstructor() {
		return isConstructor;
	}

	/**
	 * @return
	 */
	public boolean isStatic() {
		return isStatic;
	}

	public void freeLemmas() {
		lemmas = null;
	}

	/**
	 * @return
	 */
	public String getName() {
		return name;
	}

	public void updateStatus() {
		nbPo = getLemmas().getNbPo() + wellDefinednessLemmas.getNbPo();
		nbPoProved =
			getLemmas().getNbPoProved() + wellDefinednessLemmas.getNbPoProved();
	}

	public void addGoals(ArrayList al) {
		wellDefinednessLemmas.addGoals(al);
		getLemmas().addGoals(al);
	}

	/**
	 * 
	 */
	public void selectAll() {
		Lemma [] l = getLemmas().getLemmas();
		for(int i = 0; i< l.length; i++)
			l[i].selectAll();		
	}

}
