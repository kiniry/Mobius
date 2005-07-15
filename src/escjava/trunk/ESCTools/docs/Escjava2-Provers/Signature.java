class Signature {
    private String signature;


    Signature(String signature) {
	this.signature = signature;
    }

    public String toString() {
	return signature;
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
	return new String("");
    }

    public String function(){
	return new String("");
    }

    public String type(){

	return new String("");
    }
}
