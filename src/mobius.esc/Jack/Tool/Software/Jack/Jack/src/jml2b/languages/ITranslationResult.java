//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages;

/**
 * This interface defines the result of the translation of a formula in a given 
 * language. Finally the result of the translation is converted into a string.
 * 
 * @author L. Burdy
 **/
public interface ITranslationResult {

	/**
	 * Constructs a translation result from a string. Used to load a type.
	 * @param s the string to encapsulate.
	 * @return the translation result corresponding to the string.
	 **/
	ITranslationResult Factory(String s);

	/**
	 * @return The string corresponding to the result of a translation.
	 **/
	String toUniqString();
	
}
