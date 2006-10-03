//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: NamedNode.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.structure.java;

import jml.JmlDeclParserTokenTypes;
import jml2b.pog.util.IdentifierResolver;
import antlr.collections.AST;

/**
 * @author A. Requet
 */
public abstract class NamedNode
	extends ParsedItem
	implements JmlDeclParserTokenTypes {

	public int nameIndex;
	private int nameSuffix;
	public boolean garbage;

	public NamedNode() {
		nameIndex = -1;
		garbage = true;
	}
	
	public NamedNode(JmlFile jf, AST tree) {
		super(jf, tree);
		nameIndex = -1;
		nameSuffix = 0;
		garbage = true;
	}

	public NamedNode(ParsedItem pi) {
		super(pi);
		nameIndex = -1;
		nameSuffix = 0;
		garbage = true;
	}

	public abstract String getName();

	// method used when a class does not have a nameIndex.
	// the default implementation is to return the Java name.
	public String getDefaultBName() {
		return getName();
	}

	public boolean hasBName() {
		return nameIndex >= 0;
	}

	public String getBName() {
		if (nameIndex < 0) {
			return getDefaultBName();
		}
		return IdentifierResolver.bName(nameIndex);
	}

	//@ modifies nameSuffix;
	public String newName() {
		String s = getBName();
		return s + "_" + nameSuffix++;
	}

	/** clear all the names of the named node.
	 */
	/*@
	  @ modifies nameIndex, garbage;
	  @*/
	public void clearName() {
		// Always keep 0 corresponding to the virual field length of the virtual
		// class corresponding to arrays.
		if (nameIndex != 0) {
			nameIndex = -1;
			garbage = true;
		}
		nameSuffix = 0;
	}

	static final long serialVersionUID = 6128106779507407952L;
}
