/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import javafe.ast.ModifierPragmaVec;
import javafe.tc.TypeSig;

public class TypeCheck extends javafe.tc.TypeCheck {

    // === Singleton ===

    // TODO: Investigate the dubious marriage between singleton and
    // inheritance: is there no better solution? (rgrig)

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
     * @return an instance of <code>rcc.tc.FlowInsensitiveChecks</code> as the
     *         algorithm used for name resolution and typecheck.
     */
    public javafe.tc.FlowInsensitiveChecks makeFlowInsensitiveChecks() {
        return new rcc.tc.FlowInsensitiveChecks();
    }

    /**
     * We can access anything from annotations.
     */
    public boolean canAccess(/* @ non_null @ */TypeSig from,
    /* @ non_null @ */TypeSig target, int modifiers, ModifierPragmaVec pmodifiers) {
        if (FlowInsensitiveChecks.inAnnotation) { return true; }
        return super.canAccess(from, target, modifiers, pmodifiers);
    }
}
