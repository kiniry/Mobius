//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubInstancesSet
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TerminalForm;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;

/**
 * This class corresponds to the substituion of <code>instances</code> with
 * <code>instances \/ f</code>.
 * @author L. Burdy
 **/
public class SubInstancesSet extends SubInstances {

    /**
     * Constructs a substitution for <code>instances</code>
     * @param f The formula corresponding to the set of new instances
     **/
    public SubInstancesSet(Formula f) {
        super(f);
    }

    public Object clone() {
        return new SubInstancesSet((Formula) getF().clone());
    }
    
    /**
     * Substitutes <code>instances</code> with <code>instances \/ f</code>
     **/
    public Formula sub(Formula p) {
        return p.subIdent(
            "instances",
            new BinaryForm(
                B_UNION,
                TerminalForm.$instances,
                getF()));
    }

    public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
        s.writeByte(INSTANCES_SET);
        super.save(config, s, jf);
    }


}
