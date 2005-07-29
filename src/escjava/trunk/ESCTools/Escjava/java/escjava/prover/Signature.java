package escjava.prover;

public class Signature {

    public /*@ non_null @*/ LightAnalyser la; 

    /*
     *
     */ 

    public Signature(/*@ non_null @*/ String fileNameOfTheory) {

	    la = new LightAnalyser(fileNameOfTheory);
    }

    /*
     * A signature can be decomposed into
     ** variable 
     ** predicate
     ** function 
     ** type 
     * 
     * These functions will do the job
     */ 

    /*
     * Notice that in smt lib format, variables are 0 unary functions.
     */
    public String variable(){

	return new String("");
    }

    public String predicate(){

	return la.find(3);
    }

    public String function(){

	return la.find(2);
    }

    public String type(){

	return la.find(1);
    }

    public void print(){

	System.out.println("Types :");
	System.out.println(type());
	System.out.println("Variables :");
	System.out.println(variable());
	System.out.println("Functions :");
	System.out.println(function());
	System.out.println("Predicates :");
	System.out.println(predicate());

    }
}
