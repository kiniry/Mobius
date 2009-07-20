//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.exceptions.LanguageException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsTranslationResult implements ITranslationResult {

	String localDecl;
	Vector predDecl = new Vector();
	String s;
	//	VType type;

	public PvsTranslationResult() {
	}

	private String getType(Formula f) throws LanguageException {
		switch (f.getNodeType()) {
			case IFormToken.IS_MEMBER_FIELD :
				return "["
					+ getEnclosedType(((BinaryForm) f).getLeft())
					+ " -> "
					+ getEnclosedType(((BinaryForm) f).getRight())
					+ "]";
			case IFormToken.IS_ARRAY :
				return f.toLang("PVS", 0).toUniqString();
			case IFormToken.IS_STATIC_FIELD :
			default :
				return getEnclosedType(f);
		}
	}

	private String getEnclosedType(Formula f) throws LanguageException {
		if (f == TerminalForm.$References)
			return "REFERENCES";
		else if (f == TerminalForm.$instances)
			return "(instances)";
		else if (f instanceof TTypeForm) {
			switch (((TTypeForm) f).getTag()) {
				case Type.T_BOOLEAN :
					return "bool";
				case Type.T_INT :
					return "t_int";
				case Type.T_SHORT :
					return "t_short";
				case Type.T_BYTE :
					return "t_byte";
				case Type.T_CHAR :
					return "t_char";
				case Type.T_REF :
					return "{ x : REFERENCES | instances?(x) "
						+ "AND subtype(typeof(x), "
						+ f.toLang("PVS", 0).toUniqString()
						+ ")}";
				case Type.T_ARRAY :
					return "{ x : REFERENCES | instances?(x) "
						+ "AND subtype(typeof(x), "
						+ f.toLang("PVS",0).toUniqString()
						+ ")}";
				case Type.T_LONG :
				case Type.T_DOUBLE :
				case Type.T_FLOAT :

				default :
					throw new InternalError(
						"PvsTranslatioResult: cannot find the super type of tag "
							+ ((TTypeForm) f).getTag());

			}
		} else
			throw new InternalError(
				"PvsTranslatioResult: cannot find the super type of "
					+ f.toLangDefault(0));
	}
	public PvsTranslationResult(PvsBinaryForm f) throws LanguageException {
		PvsTranslationResult ctr1 =
			(PvsTranslationResult) f.getLeft().toLang("PVS", 0);
		//		PvsTranslationResult ctr2 =
		//			(PvsTranslationResult) f.getRight().toLang("PVS", 0);
		localDecl =
			ctr1.toUniqString() + ": VAR " + getType(f.getRight()) + "\n";
		s = "true % " + localDecl;
	}

	public PvsTranslationResult(QuantifiedVarForm f) throws LanguageException {
		PvsTranslationResult ctr1 =
			(PvsTranslationResult) f.getVar().toLang("PVS", 0);
		PvsTranslationResult ctr2 =
			(PvsTranslationResult) f.getType().toLang("PVS", 0);
		s = "(" + ctr1.toUniqString() + ": " + ctr2.toUniqString() + ")";
	}

	public PvsTranslationResult(String string) {
		localDecl = null;
		s = string;
	}

	public PvsTranslationResult(PvsTranslationResult r1, String string) {
		localDecl = r1.getLocalDecl();
		s = string;
	}

	/**
	 * @param string
	 */
	public PvsTranslationResult(
		PvsTranslationResult r1,
		PvsTranslationResult r2,
		String string) {
		if (r2.getLocalDecl() == null)
			localDecl = r1.getLocalDecl();
		else if (r1.getLocalDecl() == null)
			localDecl = r2.getLocalDecl();
		else
			localDecl = r1.getLocalDecl() + r2.getLocalDecl();
		s = string;
	}

	public PvsTranslationResult(
		PvsTranslationResult r1,
		PvsTranslationResult r2,
		PvsTranslationResult r3,
		String string) {
		localDecl = "";
		if (!(r1.getLocalDecl() == null))
			localDecl += r1.getLocalDecl();
		if (!(r2.getLocalDecl() == null))
			localDecl += r2.getLocalDecl();
		if (!(r3.getLocalDecl() == null))
			localDecl += r3.getLocalDecl();
		if (localDecl.equals(""))
			localDecl = null;
		s = string;
	}

	public PvsTranslationResult(
		PvsTranslationResult r1,
		PvsTranslationResult r2,
		PvsTranslationResult r3,
		PvsTranslationResult r4,
		String string) {
		localDecl = "";
		if (!(r1.getLocalDecl() == null))
			localDecl += r1.getLocalDecl();
		if (!(r2.getLocalDecl() == null))
			localDecl += r2.getLocalDecl();
		if (!(r3.getLocalDecl() == null))
			localDecl += r3.getLocalDecl();
		if (!(r4.getLocalDecl() == null))
			localDecl += r4.getLocalDecl();
		if (localDecl.equals(""))
			localDecl = null;
		s = string;
	}

	//	/**
	//	 * @param string
	//	 */
	//	public PvsTranslationResult(
	//		PvsTranslationResult r1,
	//		PvsTranslationResult r2,
	//		String decl,
	//		String string,
	//		VType t) {
	//		localDecl = decl;
	//		if (r2.getLocalDecl() == null)
	//			localDecl += r1.getLocalDecl();
	//		else if (r1.getLocalDecl() == null)
	//			localDecl += r2.getLocalDecl();
	//		else
	//			localDecl += r1.getLocalDecl() + r2.getLocalDecl();
	//
	//		s = string;
	//		type = t;
	//	}
	//
	//	public PvsTranslationResult(
	//		PvsTranslationResult r1,
	//		PvsTranslationResult r2,
	//		PvsTranslationResult r3,
	//		String decl,
	//		String string,
	//		VType t) {
	//		localDecl = decl;
	//		if (!(r1.getLocalDecl() == null))
	//			localDecl += r1.getLocalDecl();
	//		if (!(r2.getLocalDecl() == null))
	//			localDecl += r2.getLocalDecl();
	//		if (!(r3.getLocalDecl() == null))
	//			localDecl += r3.getLocalDecl();
	//		s = string;
	//		type = t;
	//	}

	public ITranslationResult Factory(String s) {
		return new PvsTranslationResult(s);
	}

	public String toUniqString() {
		return s;
	}

	/**
	 * @return
	 */
	public String getLocalDecl() {
		return localDecl;
	}

	public String[] getPredDecls() {
		int i = 0;
		String[] res = new String[predDecl.size()];
		Enumeration e = predDecl.elements();
		while (e.hasMoreElements()) {
			res[i++] = (String) e.nextElement();
		}
		return res;
	}
	public void addPredDecl(String string) {
		predDecl.add(string);
	}
	public void setLocalDecl(String string) {
		localDecl = string + "\n";
	}

}
