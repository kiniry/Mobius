//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTypeofSingle
/*
/*******************************************************************************
/* Warnings/Remarks:
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
 * <code>typeof <+ {f |-> t}</code>
 * @author L. Burdy
 **/
public class SubTypeofSingle extends SubTypeof {

    /**
     * Constructs a substitution for <code>typeof</code>
     * @param f The formula corresponding to the extended typeof domain
     * @param t The formula corresponding to the value asociated to new domain
     **/
	public SubTypeofSingle(Formula f, Formula t) {
		super(f, t);
	}

	public Object clone() {
		return new SubTypeofSingle((Formula) getF().clone(), getT());
	}

    /**
     * Substitues <code>typeof</code> by <code>typeof <+ {f |-> t}</code> in 
     * <code>p</code>.
     **/
	public Formula sub(Formula p)  {
		return p.subIdent(
			"typeof",
			new BinaryForm(
				B_OVERRIDING,
				TerminalForm.$typeof,
				new BinaryForm(
						B_COUPLE,
						getF(),
						getT())));
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(TYPEOF_SINGLE);
		super.save(config, s, jf);
 	}

}
