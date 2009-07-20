//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ElementsForm.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.structure.java.IJmlFile;
import jml2b.structure.java.Type;
import jml2b.util.IOutputStream;

/**
 * This class implements terminal formulas that correspond to variables 
 * xxxelements_n, where xxx can be int, short, byte, boolean, char ou ref and n 
 * is a natural number. The token associated with those formulas is 
 * <code>Ja_IDENT</code>
 * @author L. Burdy
 */
public final class ElementsForm extends TerminalForm {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The formula <code>intelements_n</code>.
	 **/
	public static ElementsForm intelements =
		new ElementsForm("intelements", Type.T_INT);

	/**
	 * The formula <code>shortelements_n</code>.
	 **/
	public static ElementsForm shortelements =
		new ElementsForm("shortelements", Type.T_SHORT);

	/**
	 * The formula <code>byteelements_n</code>.
	 **/
	public static ElementsForm byteelements =
		new ElementsForm("byteelements", Type.T_BYTE);

	/**
	 * The formula <code>booleanelements_n</code>.
	 **/
	public static ElementsForm booleanelements =
		new ElementsForm("booleanelements", Type.T_BOOLEAN);

	/**
	 * The formula <code>charelements_n</code>.
	 **/
	public static ElementsForm charelements =
		new ElementsForm("charelements", Type.T_CHAR);

	/**
	 * The formula <code>refelements_n</code>.
	 **/
	public static ElementsForm refelements =
		new ElementsForm("refelements", Type.T_REF);

	/**
	 * Array of all xxxelements_n formulas.
	 **/
	public static ElementsForm[] elements =
		{
			ElementsForm.intelements,
			ElementsForm.shortelements,
			ElementsForm.byteelements,
			ElementsForm.booleanelements,
			ElementsForm.charelements,
			ElementsForm.refelements };

	/**
	 * Array of type corresponding to each xxxelements_n formula.
	 **/
	public static int[] elementsType =
		{
			Type.T_INT,
			Type.T_SHORT,
			Type.T_BYTE,
			Type.T_BOOLEAN,
			Type.T_CHAR,
			Type.T_REF };

	/**
	 * Resets all the suffix of the xxxelements_n formula to 0.
	 **/
	public static void clearSuffix() {
		ElementsForm.intelements.clearNameSuffix();
		ElementsForm.shortelements.clearNameSuffix();
		ElementsForm.byteelements.clearNameSuffix();
		ElementsForm.booleanelements.clearNameSuffix();
		ElementsForm.charelements.clearNameSuffix();
		ElementsForm.refelements.clearNameSuffix();
	}

	/**
	 * Returns the xxxelements_n formula corresponding to a type.
	 * @param t The type of the elements of the searched array
	 * @return the xxxelements_n formula corresponding to t.
	 **/
	public static ElementsForm getElementsName(Type t) {
		ElementsForm elements = null;
		switch (t.getTag()) {
			case Type.T_INT :
				elements = ElementsForm.intelements;
				break;
			case Type.T_SHORT :
				elements = ElementsForm.shortelements;
				break;
			case Type.T_BYTE :
				elements = ElementsForm.byteelements;
				break;
			case Type.T_BOOLEAN :
				elements = ElementsForm.booleanelements;
				break;
			case Type.T_CHAR :
				elements = ElementsForm.charelements;
				break;
			case Type.T_ARRAY :
			case Type.T_REF :
				elements = ElementsForm.refelements;
				break;
			default :
				throw new InternalError(
					"crochet_e LBRACK : wrong array elements type "
						+ t.toString());
		}
		return elements;
	}

	/**
	 * Suffix number of the current formula.
	 **/
	private int nameSuffix = 0;

	/**
	 * Tag corresponding to the type tag of the xxx type.
	 **/
	private int tag;

	/**
	 * Creates a element formula with name <code>s_0</code>
	 * @param s The name
	 * @param tag The associated type tag.
	 **/
	ElementsForm(String s, int tag) {
		super(s);
		this.tag = tag;
	}

	public ElementsForm(ElementsForm e) {
		super(e.newName());
		tag = e.tag;
	}

/**
	 * Increments the suffix in manner to return a new name.
	 * @return a new name for a new occurence of the formula
	 **/
	//@ modifies nameSuffix;
	private String newName() {
		return getNonAmbiguousName() + "_" + nameSuffix++;
	}

	/**
	 * Reset the suffix to 0.
	 **/
	void clearNameSuffix() {
		nameSuffix = 0;
	}

	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(getNodeType());
		s.writeUTF(getNonAmbiguousName());
		getBasicType().save(s);
	}

	/**
	 * Returns the B type of the formula.
	 * @return the B type: a function of function.
	 **/
	public Formula getType() {
		Formula f = null;
		switch (tag) {
			case Type.T_INT :
			case Type.T_SHORT :
			case Type.T_BYTE :
			case Type.T_BOOLEAN :
			case Type.T_CHAR :
				f = new TTypeForm(IFormToken.T_TYPE, new Type(tag));
				break;
			case Type.T_REF :
				f = TerminalForm.REFERENCES;
				break;
		}

		return new UnaryForm(IS_ARRAY, f);
	}

}
