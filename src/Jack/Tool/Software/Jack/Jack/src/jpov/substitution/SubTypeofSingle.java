//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTypeofSingle
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
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
	public SubTypeofSingle(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		super(config, fi, s);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.TYPEOF_SINGLE);
		super.save(config, s, jf);
	}

	/**
	 * Returns "t f"
	 **/
	public String getInfo() {
		return getT().toLangDefault(3) + " " + getF().toLangDefault(6);
	}
}
