//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ILanguage.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages;

import java.io.IOException;

import jml2b.exceptions.LanguageException;
import jml2b.formula.Formula;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TerminalForm;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;
import jpov.structure.Goal;
import jpov.structure.VirtualFormula;

/**
 * This interface allows to define a new language, it has to be implement by
 * a plugin defining a new language.
 * 
 * @author L. Burdy
 **/
public interface ILanguage {

	/**
	 * Returns a formula corresponding to the initial but converted in a
	 * translatable subclass of formula. The result has to be a subtype of formula.
	 * @param f The formula to convert
	 * @return the converted formula
	 **/
	public ITranslatable formulaFactory(Formula f);

	/**
	 * Returns a type corresponding to the initial one but converted in a
	 * translatable type.
	 * @param t The type to convert
	 * @return the converted type
	 **/
	public ITranslatable typeFactory(Type t) throws LanguageException ;

	/**
	 * Returns quantified variables corresponding to the initial ones but 
	 * translatable.
	 * @param qvf The quantified variables to convert
	 * @return the converted quantified variables
	 **/
	public ITranslatable quantifiedVarFactory(QuantifiedVarForm qvf);

	/**
	 * Displays a goal in the lemma view.
	 * @param g The goal to display
	 * @return the string to print in the lemma view that correspond to the 
	 * goal.
	 */
	public String displayGoal(Goal g, boolean applySubstitution);

	/**
	 * Saves a terminal formula in a jpo file.
	 * @param s The jpo file
	 * @param f The formula to save
	 * @throws IOException
	 */
	public void save(IOutputStream s, TerminalForm f)
		throws IOException, LanguageException;

	/**
	 * Saves the result of a translation in a jpo file.
	 * @param s The jpo file
	 * @param result The result to save
	 * @throws IOException
	 */
	public void save(IOutputStream s, ITranslationResult result)
		throws IOException;

	/**
	 * Load a terminal formula from a jpo file.
	 * @param s The jpo file
	 * @return
	 */
	public ITranslationResult load(JpoInputStream s) throws IOException;

	
	/**
	 * Returns a formula corresponding to the initial but converted in a
	 * translatable subclass of formula. The result has to be a subtype of formula.
	 * @param f The formulas to convert
	 * @return the converted formula
	 **/
	public String[] displayHyp(VirtualFormula[] f) throws LanguageException;

	
	public String getName();
	
	
}
