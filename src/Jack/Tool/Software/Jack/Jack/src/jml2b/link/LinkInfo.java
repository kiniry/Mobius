///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: LinkInfo.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.link;

import jml2b.structure.java.Package;
import jml2b.structure.java.Type;
import jml2b.util.Profiler;

/**
 * @author A. Requet
 */
public class LinkInfo extends Profiler {
    public int tag;
    public Type type;
    Package pkg;

    public LinkInfo(Package p) {
        tag = PACKAGE;
        pkg = p;
    }

    public LinkInfo(Type t) {
        tag = TYPE;
        type = t;
    }

    public Package getPackage() {
        return pkg;
    }

	//@ ensures \result == type;
    public Type getType() {
        return type;
    }

    public static final int TYPE = 1;
    public static final int PACKAGE = 2;
}
