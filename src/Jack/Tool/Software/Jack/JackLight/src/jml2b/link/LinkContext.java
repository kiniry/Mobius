//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LinkContext.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.link;

import java.util.Enumeration;

import jml2b.structure.AMethod;
import jml2b.structure.java.AClass;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Package;
import jml2b.util.Profiler;

/**
 * @author A. Requet, L. Burdy
 */
public class LinkContext extends Profiler {
    private boolean resultAdmitted;
	JmlFile jmlFile;
    private boolean fileContext;

    /** 
     * Stack of local variables used for linking
     */
    public VarStack linkVars;

    public AClass currentClass;
    public Package currentPackage;
    public AMethod currentMethod;
    
    /*@
      @ invariant linkVars != null;
      @*/

    /*@
      @ requires f != null;
      @*/
    public LinkContext(JmlFile f) {
        fileContext = true;
        jmlFile = f;
        currentPackage = f.getPackage();
        linkVars = new VarStack();
    }
    
    public LinkContext(AClass ac) {
        fileContext = true;
        jmlFile = ac.getJmlFile();
        currentPackage = ac.getPackage();
        linkVars = new VarStack();
    }

    /*@
      @ requires l != null;
      @ requires f != null;
      @ requires f.tag == LinkInfo.TYPE 
      @          ==> (f.type.tag == Type.T_REF || f.type.tag == Type.T_ARRAY);
      @*/
    public LinkContext(LinkContext l, LinkInfo f) {
        fileContext = false;
        currentMethod = l.currentMethod;
        switch (f.tag) {
            case LinkInfo.TYPE :
                currentClass = f.getType().getRefType();
                break;
            case LinkInfo.PACKAGE :
                currentPackage = f.getPackage();
                break;
        }
        linkVars = new VarStack();
    }

    //@ modifies currentClass;
    public void setCurrentClass(AClass c) {
        currentClass = c;
    }

    public AClass getCurrentClass() {
        return currentClass;
    }

    /** return the package corresponding to the given imported class.
    (i.e. a class imported as import package.class_name;)
    return null if the class is not imported */
    public Package getImportedClassPackage(String class_name) {
        if (jmlFile != null) {
            return jmlFile.getImportedClassPackage(class_name);
        } else {
            return null;
        }
    }

    public Package getPackage() {
        return currentPackage;
    }

    public Enumeration getImportedPackages() {
        if (jmlFile != null) {
            return jmlFile.getImportedPackages();
        } else {
            return new DummyEnumeration();
        }
    }

    // return true if this context is the "global" link context. That is,
    // 
    public boolean isFileContext() {
        return fileContext;
    }

	public boolean isResultAdmitted() {
		return resultAdmitted;
	}
	/**
	 * @param b
	 */
	public void setResultAdmitted(boolean b) {
		resultAdmitted = b;
	}

}

class DummyEnumeration extends Profiler implements Enumeration {
    public boolean hasMoreElements() {
        return false;
    }
    public Object nextElement() {
        return null;
    }
}
