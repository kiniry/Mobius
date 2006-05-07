/* Copyright 2000, 2001, Compaq Computer Corporation */


package rcc.ast;

import javafe.util.Assert;
import javafe.util.Location;

import javafe.ast.*;

public class CloneForInstantiation extends CloneWithSubstitution  {
    
    //@ ensures RES!=null
    public Object visitInterfaceDecl(InterfaceDecl y, Object o) {
        Object x = super.visitInterfaceDecl(y,o);
        if (!(x instanceof InterfaceDecl)) {
            return x;
        }
        InterfaceDecl r = (InterfaceDecl)x;
        if (r.tmodifiers != null) {
            for (int i = 0; i < r.tmodifiers.size(); i++) {
                if (r.tmodifiers.elementAt(i) instanceof GenericParameterPragma) {
                    r.tmodifiers.removeElement(r.tmodifiers.elementAt(i));
                }
            }
        }
        return r;
    }    

        //@ ensures RES!=null
    public Object visitClassDecl(ClassDecl y, Object o) {
        Object x = super.visitClassDecl(y,o);
        if (!(x instanceof ClassDecl)) {
            return x;
        }
        ClassDecl r = (ClassDecl)x;
        if (r.tmodifiers != null) {
            for (int i = 0; i < r.tmodifiers.size(); i++) {
                if (r.tmodifiers.elementAt(i) instanceof GenericParameterPragma) {
                    r.tmodifiers.removeElement(r.tmodifiers.elementAt(i));
                }
            }
        }
        return r;
    }    
    
    
    public CloneForInstantiation(MultipleSubstitution ms) {
        super(ms);
        cloneDecorations = false;
        cloneNoSubs.setCloneDecorations(false);
    }
    
}
