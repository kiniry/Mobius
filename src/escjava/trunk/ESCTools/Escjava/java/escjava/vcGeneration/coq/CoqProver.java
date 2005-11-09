package escjava.vcGeneration.coq;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import escjava.vcGeneration.*;

public class CoqProver implements ProverType {

    public TVisitor visitor() {
        return new TCoqVisitor(this);
    }

    public String getProof(String proofName, String declns, String vc) {
    	//TCoqVisitor pvi = new TCoqVisitor(this);
    	//System.out.println("here lieth thee");
    	// generate declarations
    	StringBuffer s = new StringBuffer();
    	s.append("Load \"defs.v\".\n");
    	//Let's go for the purity:
    	Vector methNames = TMethodCall.methNames;
    	Vector methDefs = TMethodCall.methDefs;
    	for(int i = 0; i < methNames.size(); i++) {
    		s.append("Variable "  + getVariableInfo(((VariableInfo)methNames.get(i)))+" : "); 
    		TMethodCall tmc = (TMethodCall)(methDefs.get(i));
    		Vector v = tmc.getArgType();
    		for(int j = 0; j < v.size(); j++) {
    			TypeInfo ti = ((TypeInfo) v.get(j));
    			if (ti == null) 
    				s.append("S -> ");
    			else
    				s.append(((TypeInfo) v.get(j)).def + " -> ");
    	    }	
    	    if(tmc.type == null) {
    	    	s.append("S.\n");
    	    }
    	    else {
    	    	s.append(tmc.type.def +".\n");
    	    }
    	}
    	s.append("Lemma "  + proofName+" : \n"); 

    	s.append("forall ");
    		
    		
    	s.append(declns + " ,\n");

    	s.append(vc);
    	
    	s.append(".\nProof with autosc.\nQed.");
    	return s.toString();
 

    }


    public String getTypeInfo(TypeInfo caller) {
        if (caller.def == null)
            coqRename(caller);
        return caller.def;
    }

    public void init() {
        // Predefined types

        TNode.$Reference = TNode.addType("%Reference", "Reference");
        TNode.$Time = TNode.addType("%Time", "Time");
        TNode.$Type = TNode.addType("%Type", "Types");
        TNode.$boolean = TNode.addType("boolean", "Boolean");
        TNode.$char = TNode.addType("char", "T_char");
        TNode.$DOUBLETYPE = TNode.addType("DOUBLETYPE", "ContinuousNumber"); // fixme, is it JavaNumber or BaseType ?
        TNode.$double = TNode.addType("double", "ContinuousNumber"); //fixme
        TNode.$Field = TNode.addType("%Field", "Field"); // fixme there's a lot of different fields in the pvs logic, I need to capture that
        TNode.$INTTYPE = TNode.addType("INTTYPE", "T_int"); //fixme like DOUBLETYPE
        TNode.$integer = TNode.addType("integer", "DiscreteNumber"); //fixme
        TNode.$float = TNode.addType("float", "ContinuousNumber");
        TNode.$Path = TNode.addType("%Path", "Path"); // used to modelize different ways
        // of terminating a function
        //$String = addType("String" "String"); fixme, does this type appears in original proof ?

        // Predefined variables name
        // variables used by the old proof system and that we still need
        TNode.addName("ecReturn", "%Path", "ecReturn");
        TNode.addName("ecThrow", "%Path", "ecThrow");
        TNode.addName("XRES", "%Reference", "XRes");
    }
    
    public void rewrite(TNode tree) {
        TProofSimplifier psvi = new TProofSimplifier();
        tree.accept(psvi);
    }
    
    private void coqRename(TypeInfo t){

        if(t.old.equals("null") )
      	  t.def = "Reference";
        else {
  	  // common rules here //fixme, be more specific maybe
  	  if(t.old.startsWith("java.")) //check if in the form java.x.y 
  	      t.def = t.old.replace('.','_');
  	  else {
  	      System.err.println("Type not handled in escjava::vcGeneration::TypeInfo::coqRename() : "+t.old); 
  	      System.err.println("Considering it as a user defined type... ie ReferenceType");
  	      t.def = "ReferenceType";
  	  }
        }

    }
    
	   public /*@ non_null @*/ String getVariableInfo(VariableInfo vi){

			if(vi.type != TNode.$Type){
			    if(vi.def == null)
			    	coqRename(vi);

			    return vi.def;
			}
			else {
			    /*

			    When variable is a type, we first have to check if it's in the type table.
			    If yes, we take the name here (it's the case with predefined types like INTYPE, integer, Reference etc...

			    Else it's normally a user defined Type

			    */
			    
			    Set keySet = TNode.typesName.keySet();
			    Iterator iter = keySet.iterator();
			    TypeInfo tiTemp = null;
			    String keyTemp = null;

			    while(iter.hasNext()){
		      
				try {
				    keyTemp = (String)iter.next();
				}
				catch (Exception e){
				    System.err.println(e.getMessage());
				}
				tiTemp = (TypeInfo)TNode.typesName.get(keyTemp);

				if(tiTemp.old.equals(vi.old)) {
				    return getTypeInfo(tiTemp);
				}
				    
			    }

			    System.err.println("Warning in escjava.java.vcGenerator.VariableInfo.getCoq(), considering "+vi.old+" as a user defined type, or a not (yet) handled variable.");

			    coqRename(vi);

			    return vi.def;
			}
   }
	   
	   /*@
	      @ ensures coq != null;
	      @*/
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
				break;
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
					break;
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
		coq = coq.replace('@', '_');
		coq = coq.replace('#', '_');
		coq = coq.replace('.', '_');
		coq = coq.replace('-', '_');
		coq = coq.replace('<', '_');
		coq = coq.replace('>', '_');
		coq = coq.replace('?', '_');
		coq = coq.replace('[', '_');
		coq = coq.replace(']', '_');
		coq = coq.replace('!', '_');
		coq = coq.replaceAll("\\|", "");
//		if(coq.startsWith("XRES"))
//			coq = "XRES";
		if(coq.equals("Z"))
			coq = "z";
		vi.def = coq;
	}
	    
   public void generateDeclarations(/*@ non_null @*/StringBuffer s, HashMap variablesName) {
	    Set keySet = variablesName.keySet();

        Iterator iter = keySet.iterator();
        String keyTemp = null;
        VariableInfo viTemp = null;
        TypeInfo tiTemp = null;

        /*
         * Needed to avoid adding a comma after last declaration. As some declaration can be skipped
         * it's easier to put comma before adding variable (thus need for testing firstDeclaration
         * instead of last one)
         */
        boolean firstDeclarationDone = false;

        while (iter.hasNext()) {

            try {
                keyTemp = (String) iter.next();
            } catch (Exception e) {
                System.err.println(e.getMessage());
            }
            viTemp = (VariableInfo) variablesName.get(keyTemp);

            /* output informations in this format : oldName, pvsUnsortedName,
             * pvsName, sammyName, type.
             */
            String name = viTemp.getVariableInfo().toString();
            if(name.equals("ecReturn") || name.equals("ecThrow"))
            	continue;
            if (viTemp.type != null) {
                
                //if (!viTemp.getVariableInfo().equals("%NotHandled")) { // skipping non handled variables
                	s.append("(");
                    s.append(viTemp.getVariableInfo() + " : "
                            + viTemp.type.getTypeInfo());

//                    if (!firstDeclarationDone)
//                        firstDeclarationDone = true;
                    s.append(")");
                
            } else {
                s.append("(" + viTemp.getVariableInfo() + " : S)");

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
