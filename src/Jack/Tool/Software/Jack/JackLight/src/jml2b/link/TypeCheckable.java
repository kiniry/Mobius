//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.link;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.Type;

/**
 * @author L. Burdy
 */
public interface TypeCheckable {

	Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException;

}
