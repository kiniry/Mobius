/* Copyright 2000, 2001, Compaq Computer Corporation */


package rcc.ast;

import javafe.util.Assert;
import javafe.util.Location;

import javafe.ast.*;

/**
 * Clones everything except decorations and generic parameter pragmas.
 */
public class CloneForInstantiation extends CloneWithSubstitution  {
    
    /**
     * Remove generic parameter pragmas from the cloned result.
     */
    //@ ensures RES!=null
    public Object visitInterfaceDecl(InterfaceDecl y, Object o) {
        Object x = super.visitInterfaceDecl(y, o);
        
        if (x instanceof InterfaceDecl) {
            InterfaceDecl id = (InterfaceDecl)x;
            id.tmodifiers = cleanPragmas(id.tmodifiers);
        } else {
            Assert.fail("Cloning an interface results in something different.");
        }
        
        return x;
    }    

    /**
     * Remove generic parameter pragmas from the cloned result.
     */
    //@ ensures RES!=null
    public Object visitClassDecl(ClassDecl y, Object o) {
        Object x = super.visitClassDecl(y, o);
        
        if (x instanceof ClassDecl) {
            ClassDecl cd = (ClassDecl)x;
            cd.tmodifiers = cleanPragmas(cd.tmodifiers);
        } else {
            Assert.fail("Cloning a class results in something different.");
        }
        
        return x;
    }    
    
    
    /**
     * Makes sure decorations are not cloned.
     */
    public CloneForInstantiation(MultipleSubstitution ms) {
        super(ms);
        cloneDecorations = false;
        cloneNoSubs.setCloneDecorations(false);
    }
    
    /**
     * Returns a vector of pragmas omitting the generic parameter ones.
     * A new vector is created that shares elements with the old one.
     */
    //@ ensures (\result == null) == (\old(v) == null);
    private TypeModifierPragmaVec cleanPragmas(TypeModifierPragmaVec v) {
        if (v == null) {
            return null;
        }
        
        TypeModifierPragmaVec r = TypeModifierPragmaVec.make();
        for (int i = 0; i < v.size(); ++i) {
            TypeModifierPragma p = v.elementAt(i);
            if (!(p instanceof GenericParameterPragma)) {
                r.addElement(p);
            }
        }
        
        return r;
    }
    
}
