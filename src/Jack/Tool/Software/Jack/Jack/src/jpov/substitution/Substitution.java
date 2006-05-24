//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Substitution.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;

/**
 * This interface provides method to save and display substitution applied to 
 * goals.
 * @author L. Burdy
 */
public interface Substitution {

    /**
     * Saves the substitution in a 
     * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
     * @param config 
     * @param s The output stream corresponding to the file.
     * @param jf 
     **/
    /*@
      @ requires s != null;
      @*/
    void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException;
    
    /**
     * Returns the informations to displayed in the Java view to simulate the 
     * substitution
     * @return a string that is displayed with the initial formula 
     * corresponding to the goal.
     **/
    String getInfo();

}
