//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TerminalForm;
import jml2b.languages.ITranslationResult;
import coqPlugin.language.CoqBinaryForm;
import coqPlugin.language.CoqVar;
import coqPlugin.language.Translation;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqTranslationResult extends Translation implements ITranslationResult {


	



	

	public CoqTranslationResult(CoqBinaryForm f) throws LanguageException {
		CoqTranslationResult ctr1 =
			(CoqTranslationResult) f.getLeft().toLang("Coq", 0);
		CoqTranslationResult ctr2 =
			(CoqTranslationResult) f.getRight().toLang("Coq", 0);
		String ctr1Str = ctr1.toString();
		CoqVar var = new CoqVar(ctr1Str, f.getRight());
		
		localDecl += var;
		bIsVariableDecl = true;
		addPropPart(ctr1);
		addPropPart(ctr2);
	}

	public CoqTranslationResult(QuantifiedVarForm f) throws LanguageException {
		bIsVariableDecl = true;
		localDecl = "";
		funPart = "";
		while(f != null) {
			CoqTranslationResult ctr =
				(CoqTranslationResult) f.getVar().toLang("Coq", 0);
			CoqVar var = new CoqVar(ctr.toString(), f.getType());
			
			CoqTranslationResult ctr2 =
				(CoqTranslationResult) f.getType().toLang("Coq", 0);
			localDecl += var;
			
			if (f.getType() != TerminalForm.$References) {
				// la verification de domaine pour les entiers par ex.
				funPart += "(" + ctr2 + " " + ctr + ")";
			}
			addPropPart(ctr);
			addPropPart(ctr2);
			f = f.getNext();
		}
		
	}
	public static CoqTranslationResult buildFromLocalProp(String loc, String prop) {
		return new CoqTranslationResult(loc, prop, "");
	}
	public static CoqTranslationResult buildFromLocal(String loc) {
		return buildFromLocalProp(loc, "");
	}
	public CoqTranslationResult() {
		this("");
	}
	public CoqTranslationResult(String funPart) {
		this("", funPart);
	}
	
	public CoqTranslationResult(String prop,  String fun) {
		this("", prop, fun);
	}
	
	public CoqTranslationResult(String loc, String prop,  String fun) {
		localDecl = loc;
		funPart = fun;
		addPropPart(prop);
	}
	
	public CoqTranslationResult(CoqTranslationResult r1, String string) {
		addLocalDecl(r1);
		funPart = string;
		addPropPart(r1);
	}
	public CoqTranslationResult(CoqTranslationResult r1, String prop, String fun) {
		addLocalDecl(r1);
		funPart = fun;
		addPropPart(prop);
		addPropPart(r1);
	}

	/**
	 * @param string
	 */
	public CoqTranslationResult(
		CoqTranslationResult r1,
		CoqTranslationResult r2,
		String string) {
		addLocalDecl(r1);
		addLocalDecl(r2);
		funPart = string;
		addPropPart(r1);
		addPropPart(r2);
	}

	
	/**
	 * 
	 * @param r1
	 * @param r2
	 * @param r3
	 * @param string
	 */
	public CoqTranslationResult(
		CoqTranslationResult r1,
		CoqTranslationResult r2,
		CoqTranslationResult r3,
		String string) {
		addLocalDecl(r1);
		addLocalDecl(r2);
		addLocalDecl(r3);
		funPart = string;
		addPropPart(r1);
		addPropPart(r2);
		addPropPart(r3);
	}
	/**
	 * 
	 * @param r1
	 * @param r2
	 * @param r3
	 * @param string
	 */
	public CoqTranslationResult(
		CoqTranslationResult r1,
		CoqTranslationResult r2,
		String propPart,
		String string) {
		addLocalDecl(r1);
		addLocalDecl(r2);
		funPart = string;
		addPropPart(r1);
		addPropPart(r2);
		addPropPart(propPart);
	}
	/**
	 * 
	 * @param r1
	 * @param r2
	 * @param r3
	 * @param string
	 */
	public CoqTranslationResult(
		CoqTranslationResult r1,
		CoqTranslationResult r2,
		CoqTranslationResult r3,
		String propPart,
		String string) {
		addLocalDecl(r1);
		addLocalDecl(r2);
		addLocalDecl(r3);
		funPart = string;
		addPropPart(r1);
		addPropPart(r2);
		addPropPart(r3);
		addPropPart(propPart);
	}
	/**
	 * 
	 * @param r1
	 * @param r2
	 * @param r3
	 * @param r4
	 * @param string
	 */
	public CoqTranslationResult(
		CoqTranslationResult r1,
		CoqTranslationResult r2,
		CoqTranslationResult r3,
		CoqTranslationResult r4,
		String string) {
		addLocalDecl(r1);
		addLocalDecl(r2);
		addLocalDecl(r3);
		addLocalDecl(r4);
		funPart= string;
		addPropPart(r1);
		addPropPart(r2);
		addPropPart(r3);
		addPropPart(r4);
	}


	public CoqTranslationResult(
			CoqTranslationResult r1,
			CoqTranslationResult r2) {
			addLocalDecl(r1);
			addLocalDecl(r2);
			funPart = "";
			bIsVariableDecl = true;
			addPropPart(r1);
			addPropPart(r2);
		}
	


	public ITranslationResult Factory(String s) {
		return new CoqTranslationResult(s);
	}



	/**
	 * @return
	 */
	
	public String getFunPart() {
		return funPart;
	}
	


	
	

	
	public String getForAllDecl() {
		if (localDecl.equals(""))
			return this.toString();
		return "forall "+ localDecl + ",\n\t" + this;
	}



	
	/**
	 * @deprecated
	 */
	public String toUniqString() {
		return toString();
	}


	

}
