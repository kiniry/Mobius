//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SubTmpVar
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * This class corresponds to the substitution of a tempory variable with a 
 * formula.
 * @author L. Burdy
 */
public class SubTmpVar implements Substitution {

    /**
     * The temporary variable
     **/
	private String tmp;
	
    /**
     * The new formula
     **/
    private Formula f;

    /*@
      @ private invariant tmp != null
      @                && f != null;
      @*/

    /**
     * Constructs a substitution from a loaded
     * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
     * @param s The input stream corresponding to the jpo file
     **/
	public SubTmpVar(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
        throws IOException, jml2b.exceptions.LoadException {
		tmp = s.readUTF();
		f = Formula.create(config, s, fi);
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(jml2b.pog.substitution.Substitution.TMP_VAR);
		s.writeUTF(tmp);
		f.save(config, s, jf);
	}
	
    /**
     * @return tmp <- f
     **/
	public String getInfo() {
		return tmp + " <- " + f.toLangDefault(3);
	}

}
