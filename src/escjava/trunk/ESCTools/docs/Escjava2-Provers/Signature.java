class Signature {

    public /*@ non_null @*/ String theoryType;

    public /*@ non_null @*/ LightAnalyser la; 

    /*
     * theoryType == "smt-lib" ||
     *            ==           ; 
     */ 

    Signature(/*@ non_null @*/ String fileNameOfTheory,/*@ non_null @*/ String theoryType) {
	this.theoryType = theoryType;

	if(theoryType.compareTo("smt-lib") == 0)
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

	if(theoryType.compareTo("smt-lib") == 0)
	    return new String("");

	return null;
    }

    public String predicate(){

	if(theoryType.compareTo("smt-lib") == 0)
	    return la.find(3);

	return null;
    }

    public String function(){

	if(theoryType.compareTo("smt-lib") == 0)
	    return la.find(2);

	return null;
    }

    public String type(){

	if(theoryType.compareTo("smt-lib") == 0)
	    return la.find(1);

	return null;
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
