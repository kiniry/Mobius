package escjava.vcGeneration.coq;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.io.*;

import escjava.vcGeneration.*;
import escjava.translate.*;
import javafe.ast.*;


/**
 * This class is an implementations of the interface {@link ProverType}.
 * In order to handle the Coq theorem prover.
 * @author J. Charles, based on the work of C. Hurlin and C.Pulley
 * @version 14/11/2005
 */
public class CoqProver extends ProverType {
    
    public String labelRename(String label) {
        label = label.replace('.','_');
        label = label.replace('<','_');
        label = label.replace('>','_');
        return label;
    }
    
	/**
	 * @return an instance of the class {@link TCoqVisitor}.
	 */
    public TVisitor visitor(Writer out) throws IOException {
        return new TCoqVisitor(out, this);
    }

    /**
     * @param proofname the name we should give to the generated lemma.
     * @param declns the declarations of the forall.
     * @param vc the generated verification condition.
     * @return the Coq vernacular file representing the proof.
     */
    public void getProof(Writer out, String proofName, TNode term) throws IOException {

        //    	// We try to generate the prelude.
        //   		try {
        //			new Prelude(new File("defs.v")).generate();
        //		} catch (IOException e) {
        //			e.printStackTrace();
        //		}

        // generate declarations
        out.write("Load \"defs.v\".\n");
        generatePureMethodsDeclarations(out);
        out.write("Lemma " + proofName + " : \n");
        out.write("forall ");
        generateDeclarations(out, term);
        out.write(" ,\n");
        generateTerm(out, term);
        out.write(".\n");
        out.write("Proof with autosc.\n" + "Qed.");
    }

    
    /**
     * Generates the pure methods declarations
     * @param s The output for the declarations.
     */
    private void generatePureMethodsDeclarations(Writer s) throws IOException {
        //Let's go for the purity:
        Vector methNames = TMethodCall.methNames;
        Vector methDefs = TMethodCall.methDefs;
        for (int i = 0; i < methNames.size(); i++) {
            s.write("Variable "
                    + getVariableInfo(((VariableInfo) methNames.get(i)))
                    + " : ");
            TMethodCall tmc = (TMethodCall) (methDefs.get(i));
            Vector v = tmc.getArgType();
            for (int j = 0; j < v.size(); j++) {
                TypeInfo ti = ((TypeInfo) v.get(j));
                if (ti == null)
                    s.write("S -> ");
                else
                    s.write(((TypeInfo) v.get(j)).def + " -> ");
            }
            if (tmc.type == null) {
                s.write("S.\n");
            } else {
                s.write(tmc.type.def + ".\n");
            }
        }
    }

    
    /**
     * @param caller the type to translate to Coq.
     * @return a valid type name.
     */
    public String getTypeInfo(TypeInfo caller) {
        if (caller.def == null)
            coqRename(caller);
        return caller.def;
    }

    
    /**
     * Defines predefined Coq types, and some predefined variables
     * (ecReturn, ecThrow and XRES).
     * For now there is no String types should be extended in the future.
     */
    public void init() {
        // Predefined types
        TNode.$Reference = TNode.addType("%Reference", "Reference");
        TNode.$Time = TNode.addType("%Time", "Time");
        TNode.$Type = TNode.addType("%Type", "Types");
        TNode.$boolean = TNode.addType("boolean", "bool");
        TNode.$char = TNode.addType("char", "t_char");
        TNode.$DOUBLETYPE = TNode.addType("DOUBLETYPE", "t_double"); 
        TNode.$double = TNode.addType("double", "t_double"); 
        TNode.$Field = TNode.addType("%Field", "Field"); 
        TNode.$INTTYPE = TNode.addType("INTTYPE", "t_int");
        TNode.$integer = TNode.addType("integer", "t_int"); 
        TNode.$float = TNode.addType("float", "t_float");
        TNode.$Path = TNode.addType("%Path", "Path"); 
        // of terminating a function
        //$String = addType("String" "String"); fixme, does this type appears in original proof ?

        // Predefined variables name
        // variables used by the old proof system and that we still need
        TNode.addName("ecReturn", "%Path", "ecReturn");
        TNode.addName("ecThrow", "%Path", "ecThrow");
        TNode.addName("XRES", "%Reference", "XRes");
    }
    
    public Expr addTypeInfo(InitialState initState, Expr tree) {
        //FIXME Our prover logic is (presumably?) typed, so why do we need to do this here?
        tree = GC.implies(initState.getInitialState(), tree);
        return tree;
    }
    
    /**
     * Tries to simplify the given tree using the class
     * {@link TProofTyperVisitor}.
     * @param tree the tree to simplify.
     */
    public TNode rewrite(TNode tree) {
        TProofTyperVisitor tptv = new TProofTyperVisitor();
        try {
            tree.accept(tptv);
        } catch (IOException e) {
            // This should never happen!?
        }
        //TProofSimplifier psvi = new TProofSimplifier();
        //tree.accept(psvi);
        return tree;
    }
    
    
    /**
     * Rename the type, ie. the name {@link TypeInfo#old} to
     * a proper Coq name in the variable {@link TypeInfo#def} 
     * @param t the type name to rename.
     */
    private void coqRename(TypeInfo t){

        if(t.old.equals("null") )
      	  t.def = "Reference";
        else {
        	// common rules here //fixme, be more specific maybe
        	if(t.old.startsWith("java.")) //check if in the form java.x.y 
        		t.def = t.old.replace('.','_');
        	else {
        		System.err.println("Type not handled in escjava::vcGeneration::TypeInfo::coqRename() : "+t.old); 
        		System.err.println("Considering it as a user defined type... ie Types");
        		t.def = "ReferenceType";
        	}
        }
    }
    
    /**
     * Returns a valid Coq name corresponding to the given VariableInfo.
     * @param vi the variable info to analyse.
     */
    public /*@ non_null @*/ String getVariableInfo(VariableInfo vi){ 	
    	if(vi.type != TNode.$Type){
    		if(vi.def == null)
    			coqRename(vi);
    		
    		return vi.def;
		}
    	else {
    		/* 
    		 * When variable is a type, we first have to check if it's in the type table.
    		 * If yes, we take the name here (it's the case with predefined types like INTYPE, integer, Reference etc...
    		 * Else it's normally a user defined Type
    		 */
			    
    		Set keySet = TNode.typesName.keySet();
    		Iterator iter = keySet.iterator();
    		TypeInfo tiTemp = null;
    		String keyTemp = null;
    		
    		while(iter.hasNext()) {
    			try {
				    keyTemp = (String)iter.next();
				} catch (Exception e){
				    System.err.println(e.getMessage());
				}
				tiTemp = (TypeInfo)TNode.typesName.get(keyTemp);
				if(tiTemp.old.equals(vi.old)) {
				    return getTypeInfo(tiTemp);
				}
				    
    		}

    		System.err.println("Warning in " +
    				"escjava.java.vcGenerator.coq.CoqProver.getCoq(VariableInfo), " +
    				"considering "+
    				vi.old
    				+" as a user defined type, " +
    				"or a not (yet) handled variable.");
    			
    		coqRename(vi);
    		
    		return vi.def;
    	}
    }
	   
    /** 
     * Rename the variable, ie. the name {@link VariableInfo#old} to
     * a proper Coq name in the variable {@link VariableInfo#def}.
     * Stolen from the PVS plugin...
     * @param vi the variable to rename.
     */
    private void coqRename(VariableInfo vi){

    	String coq;
		// definitions of different regexp used.
		Pattern p1 = Pattern.compile("\\|(.*):(.*)\\.(.*)\\|");
		Matcher m1 = p1.matcher(vi.old);
		
		// <variables not handled>
		Pattern p2 = Pattern.compile("Unknown tag <.*>");
		Matcher m2 = p2.matcher(vi.old);
		
		Pattern p3 = Pattern.compile("\\|brokenObj<.*>\\|");
		Matcher m3 = p3.matcher(vi.old);
		// </variables not handled>
		Pattern p4 = Pattern.compile("\\|(.*):(.*)\\|");
		Matcher m4 = p4.matcher(vi.old);
		String name = null;
		String line = null;
		String column = null;

		int i = 0;
		

		//System.out.println("Performing regular expression matching against "+old+" ");

		/*
		  This case is done first because some variables not handled are "%Type" ones
		  and thus otherwise they will be matched by the next if construct
		*/
		if(m2.matches() || m3.matches() || vi.old.equals("brokenObj")) { // variable is not handled yet, ask David Cok about
		    // some things
		    coq = "(* %NotHandled *) brokenObj"; 
		    vi.type = TNode.$Reference;
		    
		}

		// <case 1>
		/*
		  If variable's a type, we must prefix his renaming by userDef?.
		  Why ?
		  Because if the user defined a type named 'Reference', otherwise we will use is as it
		  in the proof and it will interfer with our predefined types.

		  Since '?' isn't a valid character in the java notation and is Ok for pvs,
		  we use it to make the difference.
		*/
		else if(vi.type == TNode.$Type){
		    System.err.println("Warning in escjava.java.vcGeneration.VariableInfo.coqRename() : considering "+vi.old+" as a user defined type.");

		    // renaming done here
		    coq = "userDef_"+ vi.old;
		}
		// </case 1>

		// <case 2>, capturing |y:8.31|
		else if(m1.matches()){
		    //@ assert m.groupCount() == 3;

		    if(m1.groupCount() != 3)
		    	System.err.println("Error in escjava.java.vcGeneration.VariableInfo.coqRename : m.groupCount() != 3");

		    for( i = 1; i <= m1.groupCount(); i++) {

		    	if(m1.start(i) == -1 || m1.end(i) == -1)
		    		System.err.println("Error in escjava.java.vcGeneration.VariableInfo.coqRename : return value of regex matching is -1");
		    	else {
			    
		    		String temp = vi.old.substring(m1.start(i),m1.end(i));
		    		//@ assert temp != null;

		    		switch(i){ 
		    			case 1 :
		    				name = temp;
		    				//@ assert name != null;
		    				break;
		    			case 2:
		    				line = temp;
		    				//@ assert line != null;
		    				break;
		    			case 3:
		    				column = temp;
		    				//@ assert column != null;
		    				break;
		    			default :
		    				System.err.println("Error in escjava.java.vcGeneration.VariableInfo.coqRename : switch call incorrect, switch on value "+i);
		    		}
		    	} // no error in group			
		    } // checking all group

		    /* renaming done here, if you want the way it's done
		       (for pattern like |y:8.31|)
		       do it here. */
		    coq = name+"_"+line+"_"+column;
		} // </case 2>

		else if(m4.matches()) {
		    if(m4.groupCount() != 2)
				System.err.println("Error in escjava.java.vcGeneration.VariableInfo.coqRename : m.groupCount() != 3");

		    for( i = 1; i <= m4.groupCount(); i++) {

				if(m4.start(i) == -1 || m4.end(i) == -1)
				    System.err.println("Error in escjava.java.vcGeneration.VariableInfo.coqRename : return value of regex matching is -1");
				else {
				    
				    String temp = vi.old.substring(m4.start(i),m4.end(i));
				    //@ assert temp != null;

				    switch(i){ 
				    	case 1 :
				    		name = temp;
				    		//@ assert name != null;
				    		break;
				    	case 2:
				    		line = temp;
				    		//@ assert line != null;
				    		break;
				    	default :
				    		System.err.println("Error in escjava.java.vcGeneration.VariableInfo.coqRename : switch call incorrect, switch on value "+i);
				    }
				} // no error in group
			
		    } // checking all group

			    
		    if(line.equals("unknown"))
		    	coq = name;
		    else
		    	coq = name+"_"+line;
		}
		else {
		    coq = vi.old; // FIXME handle everything
		} // regexp didn't match
		coq = removeInvalidChar(coq);

		if(coq.equals("Z"))
			coq = "z";
		vi.def = coq;
    }
	
    /**
     * Removes the invalid characters in Coq for a given String.
     * @param name The name where some invalid characters appear.
     * @return The name without the invalid characters.
     */
    public String removeInvalidChar (String name) {
    	name = name.replace('@', '_');
		name = name.replace('#', '_');
		name = name.replace('.', '_');
		name = name.replace('-', '_');
		name = name.replace('<', '_');
		name = name.replace('>', '_');
		name = name.replace('?', '_');
		name = name.replace('[', '_');
		name = name.replace(']', '_');
		name = name.replace('!', '_');
		name = name.replaceAll("\\|", "");
		return name;
    }
    
    
    /**
     * Generates the declarations for the forall construct in the Coq Fashion,
     * i.e. (var1: Type1) (var2 : Type2)...
     * @param s The output
     * @param variablesNames the variables' names.
     */
    public void generateDeclarations(/*@ non_null @*/Writer s, HashMap variablesNames) throws IOException {
        Set keySet = variablesNames.keySet();

        Iterator iter = keySet.iterator();
        String keyTemp = null;
        VariableInfo viTemp = null;

        while (iter.hasNext()) {

            try {
                keyTemp = (String) iter.next();
            } catch (Exception e) {
                System.err.println(e.getMessage());
            }
            viTemp = (VariableInfo) variablesNames.get(keyTemp);

            String name = viTemp.getVariableInfo().toString();
            if (name.equals("ecReturn") || name.equals("ecThrow")
                    || name.equals("t_int"))
                continue;
            if (viTemp.type != null) {
                s.write("(");
                s.write(viTemp.getVariableInfo() + " : "
                        + viTemp.type.getTypeInfo());
                s.write(")");

            } else {
                s.write("(" + viTemp.getVariableInfo() + " : S)");
                TDisplay
                        .warn(
                                this,
                                "generateDeclarations",
                                "Type of variable "
                                        + keyTemp
                                        + " is not set when declarating variables for the proof, skipping it...");
            }
        }
    }
}
