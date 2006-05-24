//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Class
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.IOException;
import java.util.ArrayList;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class implements a node tree corresponding to a class.
 * @author L. Burdy
 **/
public class Class extends TreeObject {

	/**
	 * Loads a class from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a> and sets the
	 * parent of the class children.
	 * @param s The input stream corresponding to the JPO file
	 * @return the constructed class
	 **/
	static Class loadClass(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		Class c = new Class(config, fi, s);
		c.staticInitLemmas.setParent(c);
		c.wellDefInvLemmas.setParent(c);
		for (int j = 0; j < c.constructors.length; j++)
			c.constructors[j].setParent(c);
		for (int j = 0; j < c.methods.length; j++)
			c.methods[j].setParent(c);

		return c;
	}

	/**
	* The name of the class
	**/
	private String name;

	/**
	 * The array of methods of the class
	 **/
	private Method[] methods;

	/**
	 * The array of constructors of the class
	 **/
	private Method[] constructors;

	/**
	 * The proofs corresponding to the static initialization
	 **/
	private Proofs staticInitLemmas;

	private Proofs wellDefInvLemmas;

	private Field[] fields;

	/*@
	  @ private invariant name != null
	  @                && methods != null
	  @                && constructors != null
	  @                && lemmas != null;
	  @*/

	/**
	 * Constructs a class from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the JPO file
	 **/
	private Class(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		name = s.readUTF();
		int size = s.readInt();
		fields = new Field[size];
		for (int i = 0; i < size; i++)
			fields[i] = new Field(s);
		staticInitLemmas = new StaticInitProofs(config, fi, s);
		wellDefInvLemmas = new WellDefInvProofs(config, fi, s);
		constructors = new Method[s.readInt()];
		for (int j = 0; j < constructors.length; j++)
			constructors[j] = Method.loadMethod(config, fi, s);
		methods = new Method[s.readInt()];
		for (int j = 0; j < methods.length; j++)
			methods[j] = Method.loadMethod(config, fi, s);
	}

	/**
	 * Saves the class into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The ouput stream corresponding to a jpo file
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeUTF(name);
		s.writeInt(fields.length);
		for (int i = 0; i < fields.length; i++)
			fields[i].save(s);
		staticInitLemmas.save(config, s, jf);
		wellDefInvLemmas.save(config, s, jf);
		s.writeInt(constructors.length);
		for (int i = 0; i < constructors.length; i++)
			constructors[i].save(config, s, jf);
		s.writeInt(methods.length);
		for (int i = 0; i < methods.length; i++) {
			methods[i].save(config, s, jf);
		}
	}

	/**
	 * Sets all the goals of this class to unprove.
	 **/
	void unprove() {
		staticInitLemmas.unprove();
		wellDefInvLemmas.unprove();
		for (int i = 0; i < constructors.length; i++)
			constructors[i].unprove();
		for (int i = 0; i < methods.length; i++) {
			methods[i].unprove();
		}
	}

	public int getNbPo() {
		int res = 0;
		for (int i = 0; i < constructors.length; i++)
			res += constructors[i].getNbPo();
		for (int i = 0; i < methods.length; i++)
			res += methods[i].getNbPo();
		return res + staticInitLemmas.getNbPo() + wellDefInvLemmas.getNbPo();
	}

	public void setChecked() {
		staticInitLemmas.setChecked();
		wellDefInvLemmas.setChecked();
		for (int i = 0; i < constructors.length; i++)
			constructors[i].setChecked();
		for (int i = 0; i < methods.length; i++)
			methods[i].setChecked();
	}

	public void setUnchecked() {
		staticInitLemmas.setUnchecked();
		wellDefInvLemmas.setUnchecked();
		for (int i = 0; i < constructors.length; i++)
			constructors[i].setUnchecked();
		for (int i = 0; i < methods.length; i++)
			methods[i].setUnchecked();
	}

	public int getNbPoProved() {
		int res = 0;
		for (int i = 0; i < constructors.length; i++)
			res += constructors[i].getNbPoProved();
		for (int i = 0; i < methods.length; i++)
			res += methods[i].getNbPoProved();
		return res
			+ staticInitLemmas.getNbPoProved()
			+ wellDefInvLemmas.getNbPoProved();
	}

	public int getNbPoProved(String prover) {
		int res = 0;
		for (int i = 0; i < constructors.length; i++)
			res += constructors[i].getNbPoProved(prover);
		for (int i = 0; i < methods.length; i++)
			res += methods[i].getNbPoProved(prover);
		return res
			+ staticInitLemmas.getNbPoProved(prover)
			+ wellDefInvLemmas.getNbPoProved(prover);
	}

	public int getNbCheckedPo() {
		int res = 0;
		for (int i = 0; i < constructors.length; i++)
			res += constructors[i].getNbCheckedPo();
		for (int i = 0; i < methods.length; i++)
			res += methods[i].getNbCheckedPo();
		return res
			+ staticInitLemmas.getNbCheckedPo()
			+ wellDefInvLemmas.getNbCheckedPo();
	}

	/**
	 * Returns the name of the class
	 * @return <code>name</code>
	 **/
	public String getText(int type) {
		return name;
	}

	/**
	 * Returns the constructors array.
	 * @return <code>constructore</code>
	 */
	public Method[] getConstructors() {
		return constructors;
	}

	/**
	 * Returns the static initialization lemmas.
	 * @return <code>lemmas</code>
	 */
	public Proofs getStaticInitLemmas() {
		return staticInitLemmas;
	}

	public Proofs getWellDefInvLemmas() {
		return wellDefInvLemmas;
	}

	/**
	 * Returns the methods array.
	 * @return <code>methods</code>
	 */
	public Method[] getMethods() {
		return methods;
	}

	/**
	 * @return
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return
	 */
	public Field[] getFields() {
		return fields;
	}

	public void freeLemmas() {
		for (int i = 0; i < constructors.length; i++)
			constructors[i].freeLemmas();
		for (int i = 0; i < methods.length; i++)
			methods[i].freeLemmas();
		
	}


	void addGoals(ArrayList al) {
		staticInitLemmas.addGoals(al);
		wellDefInvLemmas.addGoals(al);
		for (int i = 0; i < constructors.length; i++)
			constructors[i].addGoals(al);
		for (int i = 0; i < methods.length; i++)
			methods[i].addGoals(al);
		
	}

	/**
	 * 
	 */
	public void finalizeLoad() {
		for (int i = 0; i < constructors.length; i++)
			constructors[i].getLemmas();
		for (int i = 0; i < methods.length; i++) {
			methods[i].getLemmas();
		}
	}

	/**
	 * 
	 */
	public void selectAll() {
		for (int i = 0; i < methods.length; i++) {
			methods[i].selectAll();
		}
		for (int i = 0; i < constructors.length; i++) {
			constructors[i].selectAll();
		}
	}

}
