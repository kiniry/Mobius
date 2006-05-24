//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: IJml2bConfiguration.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b;

import java.io.File;
import java.util.Vector;

import jml2b.exceptions.Jml2bException;
import jml2b.structure.IPackage;
import jml2b.structure.java.Class;
import jml2b.structure.java.Type;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.statement.Expression;
import jml2b.util.JmlPathEntry;

import org.eclipse.swt.graphics.FontData;

/**
 * The interface defines the configuration of the PO generator and the lemma 
 * viewer
 * @author L. Burdy
 */
public interface IJml2bConfiguration {

	IPackage getPackage();

	Type getObject() throws Jml2bException;
	
	Class getArray() throws Jml2bException;
	
    /**
     * Returns the directory where the files have to be read and write. Those
     * files are the jpo file and the generated files.
     **/
    File getSubdirectory();
    
    /**
     * Returns the path where files have to be searched
     * @return an array of path
     */
    JmlPathEntry[] getJmlPath();
    
//    String getJmlPathAsClassPath();
    
    /**
     * Returns the font data to use to display to source code text 
     */
    FontData getViewerFont();
    
    /**
     * Indicates whether obvious PO have to be generated or not
     */
    boolean isObviousPoGenerated();
    
	boolean isWellDefPoGenerated();
    
    /**
     * Indicates whether a view of the lemma have to be displayed or not.
     * @param name The name of the language
     */
    boolean isViewShown(String name);
    
    /**
     * Returns the default requires clause
     **/
    Expression getDefaultRequires();
    
    /**
     * Returns the default modifies clause
     **/
    ModifiesClause getDefaultModifies();
    
    /**
     * Returns the default ensures clause
     **/
    Expression getDefaultEnsures();

    /**
     * Returns the default exsures clause
     **/
    /*@
      @ ensures \result != null && \result.elementType <: \type(Exsures);
      @*/
    Vector getDefaultExsures();
    
    boolean isFileGenerated(String name);

    void setFileGenerated(String name, boolean b);

	boolean isObviousProver(String name);

	boolean getDefaultExternalFile();
    
}
