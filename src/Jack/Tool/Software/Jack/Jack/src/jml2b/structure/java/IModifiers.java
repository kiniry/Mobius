//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.java;

/**
 *
 *  @author L. Burdy
 **/
public interface IModifiers {

	String emit();
	
//	public boolean isCompatible(IModifiers modifiers) ;
	
	public  boolean isExternalVisible();
	
	public boolean isPackageVisible();
	
	public boolean isProtected();
	
	public boolean isStatic();
	
//	public boolean isSet(int flag);
	
//	public boolean isExternalVisible();
	
//	public boolean isProtectedNotSpecPublic();
	
	public boolean isFinal();
	
	public boolean isPrivate();

	/**
	 * @return
	 */
	boolean isProtectedNotSpecPublic();

	/**
	 * @return
	 */
	boolean isModel();

	/**
	 * @return
	 */
	boolean isPure();
	boolean isNative();
	boolean isGhost();
//	public boolean isJml();
	
}
