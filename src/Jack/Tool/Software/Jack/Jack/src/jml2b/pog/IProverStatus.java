//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.pog;

import java.io.IOException;

import jml2b.exceptions.LoadException;
import jml2b.pog.lemma.ProverStatus;
import jml2b.util.JpoInputStream;

/**
 * @author L. Burdy
 */
public interface IProverStatus {

	public ProverStatus factory();

	public ProverStatus factory(JpoInputStream s)
		throws IOException, LoadException;
}
