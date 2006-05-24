//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LabeledProofs
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import jml2b.formula.Formula;
import jml2b.util.Profiler;

/**
 * This class stores a proof associated with a label.
 * @author L. Burdy
 */
class LabeledProofs extends Profiler {

    /**
     * The label
     **/
    private Formula label;
    
    /**
     * The proof
     **/
    private Proofs lem;

    /*@
      @ private invariant lem != null;
      @*/

    /**
     * Constructs a labelled proof from a label and a proof
     * @param label The label
     * @param lem The proof
     **/
	/*@
	  @ requires lem != null;
	  @*/
    LabeledProofs(Formula label, Proofs lem) {
        this.label = label;
        this.lem = lem;
    }

	/**
	 * Returns the label.
	 * @return <code>label</code>
	 */
	Formula getLabel() {
		return label;
	}

	/**
	 * Returns the lem.
	 * @return <code>lem</code>
	 */
	Proofs getLem() {
		return lem;
	}

}
