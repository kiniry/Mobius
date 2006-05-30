//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyTranslationResult implements ITranslationResult {

	Vector decl = new Vector();
	Vector predDecl = new Vector();
	String main;

	public SimplifyTranslationResult() {
	}

	SimplifyTranslationResult(ITranslationResult tr) {
		main = tr.toUniqString();
	}

	SimplifyTranslationResult(String m) {
		main = m;
	}

	SimplifyTranslationResult(SimplifyTranslationResult a, String c) {
		main = c;
		addDecls(a);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		String b,
		String c) {
		main = c;
		addDecls(a);
		addDecl(b);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		String b,
		String c,
		String d) {
		main = d;
		addDecls(a);
		addDecl(b);
		addDecl(c);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b) {
		main = b.main;
		addDecls(a);
		addDecls(b);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		String c) {
		main = c;
		addDecls(a);
		addDecls(b);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		String c,
		String d) {
		main = d;
		addDecls(a);
		addDecls(b);
		addDecl(c);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		String c,
		String d,
		String e) {
		main = e;
		addDecls(a);
		addDecls(b);
		addDecl(c);
		addDecl(d);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		SimplifyTranslationResult c,
		String d) {
		main = d;
		addDecls(a);
		addDecls(b);
		addDecls(c);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		SimplifyTranslationResult c,
		String d,
		String e) {
		main = e;
		addDecls(a);
		addDecls(b);
		addDecls(c);
		addDecl(d);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		SimplifyTranslationResult c,
		String d,
		String e,
		String f) {
		main = f;
		addDecls(a);
		addDecls(b);
		addDecls(c);
		addDecl(d);
		addDecl(e);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		SimplifyTranslationResult c,
		String d,
		String e,
		String f,
		String g) {
		main = g;
		addDecls(a);
		addDecls(b);
		addDecls(c);
		addDecl(d);
		addDecl(e);
		addDecl(f);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		SimplifyTranslationResult c,
		SimplifyTranslationResult d,
		String e,
		String f) {
		main = f;
		addDecls(a);
		addDecls(b);
		addDecls(c);
		addDecls(d);
		addDecl(e);
	}

	SimplifyTranslationResult(
		SimplifyTranslationResult a,
		SimplifyTranslationResult b,
		SimplifyTranslationResult c,
		SimplifyTranslationResult d,
		String e,
		String f,
		String g,
		String h) {
		main = h;
		addDecls(a);
		addDecls(b);
		addDecls(c);
		addDecls(d);
		addDecl(e);
		addDecl(f);
		addDecl(g);
	}

	void addDecl(String d) {
		if (d != null)
			decl.add(d);
	}

	void addDecls(SimplifyTranslationResult d) {
		decl.addAll(d.decl);
		predDecl.addAll(d.predDecl);
	}

	public ITranslationResult Factory(String s) {
		return new SimplifyTranslationResult(s);
	}

	public String toUniqString() {
		return main;
	}

	public String[] toStrings() {
		int i = 0;
		String[] res = new String[decl.size()];
		Enumeration e = decl.elements();
		while (e.hasMoreElements()) {
			res[i++] = (String) e.nextElement();
		}
		return res;
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
	

}
