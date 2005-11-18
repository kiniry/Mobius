package escjava.vcGeneration.pvs.unsorted;

import javafe.ast.Expr;
import escjava.translate.GC;
import escjava.translate.InitialState;
import escjava.vcGeneration.*;

public class PvsUnsortedProver extends escjava.vcGeneration.pvs.PvsProver {
    
    public String getVariableInfo(VariableInfo caller) {

        if (caller.type != TNode.$Type) {
            if (caller.def == null)
                unsortedPvsRename(caller);

            return caller.def;
        } else
            return getTypeInfo(caller.type);

    }

    // fixme, does nothing atm
    /*@
     @ ensures unsortedPvs != null;
     @*/
    private void unsortedPvsRename(VariableInfo caller) {
        caller.def = caller.old;
    }

    public String getTypeInfo(TypeInfo caller) {
        if (caller.def == null)
            unsortedPvsRename(caller);

        return caller.def;
    }

    // fixme, does nothing atm
    /*@
     @ ensures unsortedPvs != null;
     @*/
    private void unsortedPvsRename(TypeInfo caller) {
        caller.def = caller.old;
    }

    public void init() {
        // Predefined types

        TNode.$Reference = TNode.addType("%Reference", "S");
        TNode.$Time = TNode.addType("%Time", "S");
        TNode.$Type = TNode.addType("%Type", "S");
        TNode.$boolean = TNode.addType("boolean", "S");
        TNode.$char = TNode.addType("char", "S");
        TNode.$DOUBLETYPE = TNode.addType("DOUBLETYPE", "S"); // fixme, is it JavaNumber or BaseType ?
        TNode.$double = TNode.addType("double", "S"); //fixme
        TNode.$Field = TNode.addType("%Field", "S"); // fixme there's a lot of different fields in the pvs logic, I need to capture that
        TNode.$INTTYPE = TNode.addType("INTTYPE", "S"); //fixme like DOUBLETYPE
        TNode.$integer = TNode.addType("integer", "S"); //fixme
        TNode.$float = TNode.addType("float", "S");
        TNode.$Path = TNode.addType("%Path", "S"); // used to modelize different ways
        // of terminating a function
        //$String = addType("String", "S"); fixme, does this type appears in original proof ?

        // Predefined variables name
        // variables used by the old proof system and that we still need
        TNode.addName("ecReturn", "%Path", "ecReturn");
        TNode.addName("ecThrow", "%Path", "ecThrow");
        TNode.addName("XRES", "%Reference", "%XRES");

    }
    
    public Expr addTypeInfo(InitialState initState, Expr tree) {
        tree = GC.implies(initState.getInitialState(), tree);
        return tree;
    }

    public TNode rewrite(TNode tree) {
        // FIXME
        return tree;
    }
}
