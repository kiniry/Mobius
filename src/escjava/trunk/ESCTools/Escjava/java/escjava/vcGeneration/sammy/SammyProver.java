package escjava.vcGeneration.sammy;

import java.util.HashMap;

import escjava.vcGeneration.*;

public class SammyProver implements ProverType {

    public TVisitor visitor() {
        return null; //FIXME
    }
    
    public String getProof(String proofName, String vc, String proof) {
        return null; //FIXME
    }
    
    public/*@ non_null @*/String getVariableInfo(VariableInfo caller) {

        if (caller.type != TNode.$Type) {
            if (caller.def == null)
                sammyRename(caller);

            return caller.def;
        } else
            return getTypeInfo(caller.type);
    }

    // fixme, does nothing atm
    /*@ ensures sammy != null; @*/
    private void sammyRename(VariableInfo caller) {
        caller.def = caller.old;
    }

    public String getTypeInfo(TypeInfo caller) {
        if (caller.def == null)
            sammyRename(caller);

        return caller.def;
    }

    // fixme, does nothing atm
    /*@ ensures sammy != null; @*/
    private void sammyRename(TypeInfo caller) {
        caller.def = caller.old;
    }

    public void init() {
        // Predefined types

        TNode.$Reference = TNode.addType("%Reference", "?");
        TNode.$Time = TNode.addType("%Time", "?");
        TNode.$Type = TNode.addType("%Type", "?");
        TNode.$boolean = TNode.addType("boolean", "?");
        TNode.$char = TNode.addType("char", "?");
        TNode.$DOUBLETYPE = TNode.addType("DOUBLETYPE", "?"); // fixme, is it JavaNumber or BaseType ?
        TNode.$double = TNode.addType("double", "?"); //fixme
        TNode.$Field = TNode.addType("%Field", "?"); // fixme there's a lot of different fields in the pvs logic, I need to capture that
        TNode.$INTTYPE = TNode.addType("INTTYPE", "?"); //fixme like DOUBLETYPE
        TNode.$integer = TNode.addType("integer", "?"); //fixme
        TNode.$float = TNode.addType("float", "?");
        TNode.$Path = TNode.addType("%Path", "?"); // used to modelize different ways
        // of terminating a function
        //$String = addType("String", "?"); fixme, does this type appears in original proof ?

        // Predefined variables name
        // variables used by the old proof system and that we still need
        TNode.addName("ecReturn", "%Path", "ecReturn");
        TNode.addName("ecThrow", "%Path", "ecThrow");
        TNode.addName("XRES", "%Reference", "XRES");        
    }
    
    public void rewrite(TNode tree) {
        // Intentionally do nothing!
    }

	public void generateDeclarations(StringBuffer s, HashMap variablesName) {
		// TODO Auto-generated method stub
		
	}
}
