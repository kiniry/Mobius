//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StaticInitProofs
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class StaticInitProofs extends Proofs {

	StaticInitProofs(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		super(config, fi, s);
	}

	/**
	 * @return "Static Initialisation"
	 **/
	public String getText(int type) {
		return "Static Initialisation";
	}

}
