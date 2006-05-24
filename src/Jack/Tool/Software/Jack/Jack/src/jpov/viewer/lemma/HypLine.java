//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: HypLine.java
/*
/*******************************************************************************
/* Warnings/Remarks:
//*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.viewer.lemma;

import jml2b.formula.Formula;
import jpov.structure.VirtualFormula;

/**
 * This class implements a line in the Table viewer that displays the hypothesis 
 * of a lemma
 * @author L. Burdy
 */
public class HypLine {

    /**
     * Counter allowing to assign an incremented number to each line in order
     * to sort them.
     **/
    private static int sorter = 0;

    /**
     * The displayed text corresponding to the line
     **/
    private String text;
    
    /**
     * Indicates whether this line is the first line of a displayed formula.
     * It allows to assign an icon to first line of a lemma
     **/
    private boolean first;
    
    /**
     * The line number allowing to sort the line 
     */
    private int num;
    
    /**
     * The formula associated with this line
     */
    private VirtualFormula vf;

	/**
	 * Constructs a line
     * @param fo The associated formula
     * @param t The displayed string
     * @param f indicates if this line is the first one for a lemma
	 **/
	public HypLine(VirtualFormula fo, String t, boolean f) {
        this.vf = fo;
        text = t;
        first = f;
        num = sorter++;
	}

	/**
	 * Returns whether this line is the first line of a displayed formula.
	 * @return <code>first</code>
	 */
	boolean isFirst() {
		return first;
	}

	/**
	 * Returns the origin of the associated formula.
	 */
	public byte getOrigin() {
		return vf.getOrigin();
	}

	/**
	 * Returns the displayed text corresponding to the line.
	 * @return <code>text</code>
	 */
	String getText() {
		return text;
	}

    /**
     * Returns the associated formula
     */
    public Formula getFormula() {
        return vf.getF();
    }
    
    /**
     * Returns the line number
     * @return <code>num</code>
     */
    public int getNum() {
        return num;
    }

}
