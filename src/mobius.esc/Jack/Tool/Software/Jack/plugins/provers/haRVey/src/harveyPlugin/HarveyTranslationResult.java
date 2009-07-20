//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyTranslationResult implements ITranslationResult {

	Vector decl = new Vector();
	String main;

	public HarveyTranslationResult() {
	}

	HarveyTranslationResult(ITranslationResult tr) {
		main = tr.toUniqString();
	}

	HarveyTranslationResult(String m) {
		main = m;
	}

	HarveyTranslationResult(HarveyTranslationResult a, String c) {
		main = c;
		addDecl(a.decl);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		String c) {
		main = c;
		addDecl(a.decl);
		addDecl(b.decl);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		HarveyTranslationResult c,
		String d) {
		main = d;
		addDecl(a.decl);
		addDecl(b.decl);
		addDecl(c.decl);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		String b,
		String c) {
		main = c;
		addDecl(a.decl);
		addDecl(b);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		String c,
		String d) {
		main = d;
		addDecl(a.decl);
		addDecl(b.decl);
		addDecl(c);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		HarveyTranslationResult c,
		String d,
		String e) {
		main = e;
		addDecl(a.decl);
		addDecl(b.decl);
		addDecl(c.decl);
		addDecl(d);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		HarveyTranslationResult c,
		HarveyTranslationResult d,
		String e,
		String f) {
		main = f;
		addDecl(a.decl);
		addDecl(b.decl);
		addDecl(c.decl);
		addDecl(d.decl);
		addDecl(e);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		String b,
		String c,
		String d) {
		main = d;
		addDecl(a.decl);
		addDecl(b);
		addDecl(c);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		HarveyTranslationResult c,
		String d,
		String e,
		String f) {
		main = f;
		addDecl(a.decl);
		addDecl(b.decl);
		addDecl(c.decl);
		addDecl(d);
		addDecl(e);
	}

	HarveyTranslationResult(
		HarveyTranslationResult a,
		HarveyTranslationResult b,
		HarveyTranslationResult c,
		HarveyTranslationResult d,
		String e,
		String f,
		String g,
		String h) {
		main = h;
		addDecl(a.decl);
		addDecl(b.decl);
		addDecl(c.decl);
		addDecl(d.decl);
		addDecl(e);
		addDecl(f);
		addDecl(g);
	}

	void addDecl(String d) {
		if (d != null)
			decl.add(d);
	}

	void addDecl(Vector d) {
		decl.addAll(d);
	}

	public ITranslationResult Factory(String s) {
		return new HarveyTranslationResult(s);
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

}
