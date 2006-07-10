//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTypeofSet
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TerminalForm;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;

/**
 * This interface describes a substitution of <code>typeof</code> by 
 * <code>typeof <+ f * {t}</code>
 * @author L. Burdy
 **/
public class SubTypeofSet extends SubTypeof {

	/**
	 * Constructs a substitution for <code>typeof</code>
	 * @param f The formula corresponding to the extended typeof domain
	 * @param t The formula corresponding to the value asociated to new domain
	 **/
	public SubTypeofSet(Formula f, Formula t) {
		super(f, t);
	}

	public Object clone() {
		return new SubTypeofSet((Formula) getF().clone(), getT());
	}

	/**
	 * Substitutes <code>typeof</code> with <code>typeof <+ f * {t}</code> in p.
	 **/
	public Formula sub(Formula p) {
		return p.subIdent(
			"typeof",
			new BinaryForm(
				B_OVERRIDING,
				TerminalForm.$typeof,
				new BinaryForm(CONSTANT_FUNCTION, getF(), getT())));
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(TYPEOF_SET);
		super.save(config, s, jf);
	}

}
