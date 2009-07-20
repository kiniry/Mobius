//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: NoProjectException.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package bPlugin;

/**
 * This class implements an exception that is thrown when no Atelier B project
 * is defined.
 * @sees AbServer#AbServer(IJml2bConfiguration, JpoFile)
 * @author L. Burdy
 **/
public class NoProjectException extends Exception {
    
    static final long serialVersionUID = -5089190426390297758L;

	/**
     * Constructs an exception
     * @param s The associated message
     **/
    NoProjectException(String s) {
        super(s);
    }

}
