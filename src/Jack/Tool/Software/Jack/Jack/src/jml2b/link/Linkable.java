//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Linkable.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.link;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;

/**
 * @author A. Requet, L. Burdy
 */
public interface Linkable {

	void link(IJml2bConfiguration config, LinkContext f) throws Jml2bException;

	int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException;

	// different states a linkable object can be in.
	static final int STATE_UNLINKED = 0;
	static final int STATE_LINKED = 1;
	static final int STATE_LINKED_STATEMENTS = 2;
	static final int STATE_LINKED_TYPE_CHECKED = 3;
}
