/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.Hashtable;

import javafe.ast.ASTDecoration;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.Identifier;
import javafe.tc.Env;
import javafe.tc.EnvForTypeSig;
import javafe.util.Assert;

/**
 * This class overrides EnvForTypeSig so that it "sees" ghost fields if
 * rcc.tc.FlowInsensitiveChecks.inAnnotation is true.
 * 
 * NOTE Ghost fields are identified by their name. Is this shaky?
 * 
 * TODO I believe that most of the methods should be moved in TypeSig.
 */

public class GhostEnv extends EnvForTypeSig {

    /***************************************************************************
     * * Creation: * *
     **************************************************************************/

    public GhostEnv(/* @ non_null @ */Env parent,
    /* @ non_null @ */javafe.tc.TypeSig peer, boolean staticContext) {
        super(parent, peer, staticContext);
    }

    /** for instantiating a class only */
    public GhostEnv(/* @ non_null @ */Env parent,
    /* @ non_null @ */javafe.tc.TypeSig peer) {
        super(parent, peer, true);
    }

    /***************************************************************************
     * * Debugging functions: * *
     **************************************************************************/

    /**
     * * Display information about an Env to System.out. This function * is
     * intended only for debugging use.
     */
    public void display() {
        parent.display();
        System.out.println("[[ extended with the (ghost) bindings of type "
            + peervar.getExternalName() + " ]]");
    }

    /***************************************************************************
     * * Code to locate our ghost fields by name: * *
     **************************************************************************/

    /**
     * * Attempts to find a ghost field that belongs to us (including *
     * supertypes) with name n that is not equal to excluded. * Returns the
     * ghost field decl if successfull, otherwise null. * Excluded may be null.
     */
    public FieldDecl getGhostField(String n, FieldDecl excluded) {
        collectGhostFields();
        FieldDecl result = (FieldDecl)fields.get(n);
        if (result == excluded) return null;
        return result;
    }

    /***************************************************************************
     * * Code to collect all our ghost fields: * *
     **************************************************************************/

    private Hashtable fields;
    
    /**
     * Add all new ghost fields found in s (including its supertypes) 
     * to fields.
     */
    private void collectGhostFields(javafe.tc.TypeSig s) {
        ASTDecoration paramsD = PrepTypeDeclaration.typeParametersDecoration;
        ASTDecoration declD = PrepTypeDeclaration.parameterDeclDecoration;
        FormalParaDeclVec params = (FormalParaDeclVec)paramsD.get(s);
        if (params == null) return;
        
        for (int i = 0; i < params.size(); ++i) {
            FormalParaDecl param = params.elementAt(i);
            FieldDecl decl = (FieldDecl)declD.get(param);
            Assert.notFalse(decl != null);
            fields.put(decl.id.toString(), decl);
        }
        
        /*
        // Iterate over all TypeDeclElems in s:
        TypeDecl d = s.getTypeDecl();
        TypeDeclElemVec elems = d.elems;
        for (int i = 0; i < elems.size(); i++) {
            TypeDeclElem elem = elems.elementAt(i);
            if (elem instanceof GhostDeclPragma) {
                FieldDecl ghost = ((GhostDeclPragma) elem).decl;
                Assert.notFalse(!fields.containsKey(ghost.id.toString()));
                fields.put(ghost.id.toString(), ghost);
            }
        }
        */
    }

    /**
     * * Return all our ghost fields (including our supertypes) as "set".
     */
    private void collectGhostFields() {
        if (fields != null) return;
        fields = new Hashtable(5);
        collectGhostFields(peervar);
    }

    /**************************************************************************
     * Misc. routines: 
     **************************************************************************/

    /**
     * Is a given FieldDecl a ghost field?
     */
    public boolean isGhostField(FieldDecl field) {
        collectGhostFields();
        return fields.containsKey(field.id.toString());
    }

    /**
     * Override to make ghost fields visible if *
     * rcc.tc.FlowInsensitiveChecks.inAnnotation is true.
     */
    protected boolean hasField(Identifier id) {
        if (peervar.hasField(id)) return true;
        if (!FlowInsensitiveChecks.inAnnotation) return false;
        return (getGhostField(id.toString(), null) != null);
    }
}
