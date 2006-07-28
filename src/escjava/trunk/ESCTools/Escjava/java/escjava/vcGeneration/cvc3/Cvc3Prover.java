package escjava.vcGeneration.cvc3;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.io.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javafe.ast.Expr;

import escjava.translate.GC;
import escjava.translate.InitialState;
import escjava.vcGeneration.*;

public class Cvc3Prover extends ProverType {

    // label to varname hash
    HashMap lablelhash = new HashMap();
    // a counter to ensure unique names
    int labelcounter = 0;
   
    // how to pass labels to the prover 
    // since cvc labels are actually abstract variables, we will
    // map the label to a (fresh) variable name cvc#labelvar
    public String labelRename(String label) {
// possibly use once we figure out labels
/*
        if (labelhash.containsKey(label)) {
          return labelhash(get(label)).toString();
        } else {
          String s = "cvc"+labelcounter+"labelvar";
          labelhash.put(label,s);
`          labelcounter++;
          return s;
        }
*/
        return label;
    }
    
    // cvc3's visitor
    public TVisitor visitor(Writer out) throws IOException {
        return new TCvc3Visitor(out);
    }
    
    // turn the ast into a cvc formula to be asserted/queried
    public void getProof(Writer out, String proofName, TNode term) throws IOException {
        generateDeclarations(out,term);
        generateTerm(out,term);
    }
    

    // any variable names 
    public/*@ non_null @*/String getVariableInfo(VariableInfo caller) {

        if (caller.type != TNode._Type) {
            if (caller.def == null)
                cvc3Rename(caller);

            return caller.def;
        } else
            return getTypeInfo(caller.type);
    }

    // renames any identifiers to be cvc-friendly
    // cvc identifiers are [A-Za-z][A-Za-z0-9'?_$\]*
    // so we need to rename any identifers that do not begin with a letter
    // or contain [%|.]
    // we map % -> ?
    //        . -> '
    //        | -> \
    // and add 'x' to the beginning of all names that start with either a
    // non-letter or 'x' (so there is no conflict with names already 
    // starting with 'x')
    // NOTE! to ensure that we never recursively rename something, always
    // idRename against the .old value, not the .def
    private String cvc3idRename (String s) {
      s = s.replace('%','?');
      s = s.replace('.','\'');
      s = s.replace('|','\\');
      // replace other characters with underscores (could be done better)
      s = s.replace('@', '_');
      s = s.replace('#', '_');
      s = s.replace('-', '_');
      s = s.replace('<', '_');
      s = s.replace('>', '_');
      s = s.replace('[', '_');
      s = s.replace(']', '_');
      s = s.replace('!', '_');

      Pattern p0 = Pattern.compile("^([x0-9'?_$\\])");
      Matcher m0 = p0.matcher(s);
      if (m0.matches()) {
        s = "x"+s;
      }
                                                                                      return s;
    }

    /*! ensures cvc != null; !*/
    // renames variables
    // for completeness, we should also check for keword conflicts (not done)
    private void cvc3Rename(VariableInfo caller) {
        caller.def = cvc3idRename(caller.old);
    }

    public String getTypeInfo(TypeInfo caller) {
        if (caller.def == null)
            cvc3Rename(caller);

        return caller.def;
    }

    // for completeness, we should also check for keword conflicts (not done)
    // rename types
    /*! ensures cvc != null; !*/
    private void cvc3Rename(TypeInfo caller) {
        if (caller.old.equals("null")) {
          caller.def = "Reference";
        } else { 
// do we only want to allow java.x.y?
          // follow rules for variable renaming, above
          caller.def = cvc3idRename(caller.old);
        }
    }

    public void init() {
        // Predefined types

        TNode._Reference = TNode.addType("%Reference", "Reference");
        TNode._Time = TNode.addType("%Time", "Time");
        TNode._Type = TNode.addType("%Type", "JavaType");
        TNode._boolean = TNode.addType("boolean", "Boolean");
        TNode._char = TNode.addType("char", "IntegralNumber");
        TNode._DOUBLETYPE = TNode.addType("DOUBLETYPE", "Number"); // fixme, is it JavaNumber or BaseType ?
        TNode._double = TNode.addType("double", "Number"); //fixme
        TNode._Field = TNode.addType("%Field", "Field"); // fixme there's a lot of different fields in the pvs logic, I need to capture that
        TNode._INTTYPE = TNode.addType("INTTYPE", "IntegralNumber"); //fixme like DOUBLETYPE
        TNode._integer = TNode.addType("integer", "IntegralNumber"); //fixme
        TNode._float = TNode.addType("float", "Number");
        TNode._Path = TNode.addType("%Path", "Path"); // used to modelize different ways
        // of terminating a function
        //_String = addType("String", "?"); fixme, does this type appears in original proof ?

        // Predefined variables name
        // variables used by the old proof system and that we still need
        TNode.addName("ecReturn", "%Path", "ecReturn");
        TNode.addName("ecThrow", "%Path", "ecThrow");
        TNode.addName("XRES", "%Reference", "XRES");        
    }
    
    public Expr addTypeInfo(InitialState initState, Expr tree) {
        tree = GC.implies(initState.getInitialState(), tree);
        return tree;
    }

    public TNode rewrite(TNode tree) {
// worry about this later
        // Intentionally do nothing!
        return tree;
    }

    // so this goes through the map of variable info and prints out type decls.
// this will probably not work with local (quantified) variables...
// may need to rename those
    public void generateDeclarations(/*@ non_null @*/ Writer s, HashMap variablesNames) throws IOException {
       Set keySet = variablesNames.keySet();
       Iterator iter = keySet.iterator();
       String keytmp = null;
       VariableInfo vitmp = null;

       while (iter.hasNext()) {
         try {
           keytmp = (String) iter.next();
         } catch (Exception e) {
           System.err.println(e.getMessage());
         }

         vitmp = (VariableInfo) variablesNames.get(keytmp);
// from coq -- ??
         String name = vitmp.getVariableInfo().toString();
         if (name.equals("ecReturn") || name.equals("ecThrow")
             || name.equals("t_int"))
            continue;

         if (vitmp.type != null) {
           s.write(vitmp.getVariableInfo() + " : "
             + vitmp.type.getTypeInfo());
           s.write(";");
         } else {
           s.write(vitmp.getVariableInfo() + " : S;");
           TDisplay.warn(this,
                         "generateDeclarations",
                         "Type of variable " + keytmp
                          + " is not set when declarating variables for the proof, skipping it...");
         }
       }
    }
}
