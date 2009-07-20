///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ModFlags.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.structure.java;

/**
 * Interface defining constants for the different modifier flags. The constants
 * are defined as powers of two, so that they can be orred together.
 * For instance, a <code>public abstract</code> modifier can be represented
 * as the value <code>PUBLIC | ABSTRACT</code>. 
 * 
 * @author A. Requet
 */
public interface ModFlags
{
    // values for the modifiers flags. Note that those value do not 
    // correspond to the values contained in class files.
    public static final int FINAL        = 1;
    public static final int ABSTRACT     = 2;
    public static final int PUBLIC       = 4;
    public static final int PRIVATE      = 8;
    public static final int PROTECTED    = 16;
    public static final int STATIC       = 32;
    public static final int NON_NULL     = 64;
    public static final int PURE         = 128;
    public static final int SPEC_PUBLIC  = 256;
    public static final int NATIVE       = 512;
    public static final int SYNCHRONIZED = 1024;
    public static final int GHOST        = 2048;
    public static final int MODEL        = 4096;
}
