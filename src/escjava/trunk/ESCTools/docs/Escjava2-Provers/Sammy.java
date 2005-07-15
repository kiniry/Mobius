import java.util.Properties;
import org.apache.xmlrpc.*;
import java.util.Vector;
import java.util.Enumeration;
import java.util.Iterator;

class Sammy implements ProverInterface {
    
    static XmlRpcClientLite serverInstance;

    /**
     * Vector representing the parameters that are given to sammy
     * Notice that it's cleared after each call to execute()
     */
    static Vector parameters = new Vector();

    static boolean debug = false;

    // special constructor for debugging
    public Sammy(boolean debug){
	this.debug = debug;
    }

    public ProverResponse start_prover() {

	if(debug) System.out.println("Sammy::start_prover");

	try { serverInstance = new XmlRpcClientLite("localhost",8000); }
	catch (Exception e) {
	    System.err.println("Failed to init XmlRpc");
	    System.exit(0);
	}
      
	// parameters can't be empty (rpc stuff)
	parameters.add(""); 
	  
	ProverResponse res = execute("start_solver");

	if(debug)
	    if( res != ProverResponse.OK )
		System.out.println("Failed to init sammy");

	return res;

    }
	  
    
    public ProverResponse set_prover_resource_flags(Properties properties) {

	if(debug) System.out.println("Sammy::set_prover_resource_flags");

	/* we have to create a big string containing
	 * all the flags ( = key in the hashtable of Properties)
	 * and their values ( = value)
	 */
	Enumeration flags = properties.keys();

	String value = null;
	String currentFlag = null;

	for (  ; flags.hasMoreElements() ;) {
	    
	    try {
		currentFlag = (String)flags.nextElement();
		value = properties.getProperty( currentFlag );
	    }
	    
	    catch (Exception e) {
		System.err.println("Failed to inspect properties");
		System.exit(0);
	    }
	    
	    parameters.add(currentFlag);

	    /* flags can be without value, I guess it means that
	     * value = ""
	     */
	    if( value != null ) 
		parameters.add(value);
		
	}
	
	/* TODO, look how rpc call works precisely to avoid that : */
	flatParameters();

	ProverResponse res = execute("set_flags");

	if(debug)
	    if( res!= ProverResponse.OK )
		System.out.println("Failed to set flags");

	return res;
    }

    public ProverResponse signature(Signature signature) {

	if(debug)
	    System.out.print("Sammy::signature");

	/*
	 * Calls for every decomposition of the signature
	 * Notice that it returns the last response code, not the 
	 * worst one of all calls.
	 */

	/*
	 * Variables = 0 unary function in smt lib
	 */
	parameters.add(signature.variable());

	ProverResponse res = execute("func_declaration");

	if(debug)
	    if( res!= ProverResponse.OK )
		System.out.println("Failed to set variable");

	/*
	 * Predicates
	 */
	parameters.add(signature.predicate());

	res = execute("pred_declaration");

	if(debug)
	    if( res!= ProverResponse.OK )
		System.out.println("Failed to set predicates");

	/*
	 * Functions
	 */
	parameters.add(signature.function());

	res = execute("func_declaration");

	if(debug)
	    if( res!= ProverResponse.OK )
		System.out.println("Failed to set functions");

	/*
	 * Types
	 */
	parameters.add(signature.type());

	res = execute("type_declaration");

	if(debug)
	    if( res!= ProverResponse.OK )
		System.out.println("Failed to set types");

	return res;
    }

    public ProverResponse declare_axiom(Formula formula) {

	/*
	 * Is an axiom a declaration of a predicate ?
	 */ 

	return null;
    }

    public ProverResponse make_assumption(Formula formula) {

	/*
	 * Does it correspond to 'add_assertion' in sammy's interface ?
	 */

	return null;
    }

    public ProverResponse retract_assumption(int count) {

	/*
	 * == 'backtrack' in sammy's interface ?
	 */

	return null;
    }

    public ProverResponse is_valid(Formula formula,
				   Properties properties) {

	/*
	 * I guess it corresponds to the 'query' function of 
	 * sammy's interface ?
	 */

	return null;
    }

    public ProverResponse stop_prover() {

	if(debug) System.out.println("Sammy::stop_prover");

	int result;

	// parameters can't be empty (rpc stuff)
	parameters.add(""); 

	ProverResponse res = execute("stop_solver");
	    
	if(debug)
	    if( res != ProverResponse.OK )
		System.out.println("Failed to stop sammy");

	return res;
    }

    /**
     * call to sammy using xml rpc
     * commands available :
     * start_solver
     * set_flags
     * type_declaration
     * func_declaration
     * add_assertion
     * query
     * backtrack
     * stop_solver
     * See sammy's cvcl/smt/README.TXT for further informations
     */ 
    
    /*@ requires serverInstance != null;
      @ requires !parameters.isEmpty();
      @*/
    private ProverResponse execute(/*@ non_null @*/ String cmd ){

	System.out.print("Sammy::execute   "+cmd+" "+parameters);

	Integer res = new Integer(-1); // negative attitude

	assert( serverInstance != null );

	try { res = (Integer)serverInstance.execute("sammy."+cmd,parameters); }
	catch (Exception e) {
	    System.err.println("Error during rpc call\n"+e);
	    System.exit(0);
	}

	if(debug)
	    System.out.println(", return value = "+res.intValue());

	// clean the parameters before next call
	parameters.clear();

	return SammyResponse.factory(res.intValue());
    }

    /*
     * Temporary
     */ 
    private void flatParameters() {

	Iterator i = parameters.iterator();
	StringBuffer res = new StringBuffer() ;
	String temp = null ;

	for( ; i.hasNext();) {

	    try { temp = (String)i.next(); }
	    catch (Exception e) {
		System.err.println("Error during flattening parameters\n"+e);
		System.exit(0);
	    }

	    // without the first space, it fails
	    // (sammy parsing issue I guess)
	    res.append(" ").append(temp);

	}
	
	parameters.clear();
	parameters.add(res.toString());

	if(debug)
	    System.out.println("Sammy::flatParameters   "+res);
	    
    }

}
