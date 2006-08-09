/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import javafe.ast.ModifierPragmaVec;
import rcc.ast.TagConstants;

import javafe.tc.TypeSig;
import javafe.util.Info;
import java.util.Enumeration;
import javafe.ast.*;
import javafe.util.Set;
import javafe.util.Assert;
import javafe.util.Info;

public class TypeCheck extends javafe.tc.TypeCheck {
    
    // === Singleton ===
    
    // TODO: Investigate the dubious marriage between singleton and
    //   inheritance: is there no better solution? (rgrig)
    
    private TypeCheck() {
        super();
        
        // Enables overriding of static methods.
        new rcc.tc.PrepTypeDeclaration();
    }
    
    private static TypeCheck instance = null;

    /**
     * @return the only instance of this class.
     */
    public static TypeCheck get() {
        if (instance == null) {
            instance = new TypeCheck();
        }
        return instance;
    }
    
    
    // === Overrides ===
    
    /**
     * @return an instance of <code>rcc.tc.FlowInsensitiveChecks</code>
     *         as the algorithm used for name resolution and typecheck.
     */
    public javafe.tc.FlowInsensitiveChecks makeFlowInsensitiveChecks() {
        return new rcc.tc.FlowInsensitiveChecks();
    }
    
    /**
     * We can access anything from annotations.
     * @see javafe.tc.TypeCheck.canAccess
     */
    public boolean canAccess(/*@ non_null @*/ TypeSig from, 
                             /*@ non_null @*/ TypeSig target,
                             int modifiers,
                             ModifierPragmaVec pmodifiers) {
        if (FlowInsensitiveChecks.inAnnotation) {
            return true;
        }
        return super.canAccess(from, target, modifiers, pmodifiers);
    }
}



