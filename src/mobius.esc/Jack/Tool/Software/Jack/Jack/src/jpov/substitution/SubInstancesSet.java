//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubInstancesSet
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.IFormToken;
import jml2b.formula.UnaryForm;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class corresponds to the substituion of <code>instances</code> with:
 * <code>instances \/ f</code>.
 * @author L. Burdy
 **/
public class SubInstancesSet extends SubInstances implements IFormToken {

	/**
	 * Constructs a substitution for <code>instances</code>
	 * @param f The formula corresponding to the set of new instances
	 **/
	public SubInstancesSet(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		super(config, fi, s);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.INSTANCES_SET);
		super.save(config, s, jf);
	}

	/**
	 * If <code>f</code> is a singleton, returns "a new istance: f" else return
	 * "new instances: f".
	 **/
	public String getInfo() {
		if (getF().getNodeType() == B_ACCOLADE)
			return "a new instance: " + ((UnaryForm) getF()).getExp().toLangDefault(3);
		else
			return "new instances: " + getF().toLangDefault(3);
	}

}
