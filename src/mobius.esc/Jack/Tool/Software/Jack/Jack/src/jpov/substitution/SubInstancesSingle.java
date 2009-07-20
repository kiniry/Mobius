//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubInstancesSingle
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
 * This class corresponds to the substituion of <code>instances</code> with 
 * <code>instances \/ {f}</code> corresponding to an instance creation.
 * @author L. Burdy
 **/
public class SubInstancesSingle extends SubInstances {

	/**
	 * Constructs a substitution for <code>instances</code>
	 * @param f The formula corresponding to the new instance
	 **/
	public SubInstancesSingle(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		super(config, fi, s);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.INSTANCES_SINGLE);
		super.save(config, s, jf);
	}

	/**
	 * @return a new instance : f
	 **/
	public String getInfo() {
		return "a new instance: " + getF().toLangDefault(3);
	}

}
