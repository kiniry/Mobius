package escjava.sortedProver;
import java.util.Properties;

// TODO: turn these ugly integers into enums

/**
 * Used to represent the answer given by a prover.
 */
/*@ non_null_by_default @*/
public class SortedProverResponse
{
    /**
     * A response tag to indicate everything is fine.
     */
    public static final int OK = 1;

    /**
     * A response tag to indicate that something is seriously
     * wrong with the corresponding call and/or the prover and a failure
     * has taken place.  A response code of FAIL typically indicates a
     * non-correctable situation.  The {@code getInfo()} method should be
     * consulted for additional information, and no further calls, but
     * for {@link SortedProver#stopProver()} should be made.
     */
    public static final int FAIL = 2;

    /**
     * A response tag to indicate a positive response to the
     * last command.
     */
    public static final int YES = 3;

    /**
     * A response tag to indicate a negative response to the
     * last command.
     */
    public static final int NO = 4;

    /**
     * A response tag to indicate a counter-example is
     * available.  The counter-example is contained in the {@link
     * CounterExampleResponse}.
     */
    public static final int COUNTER_EXAMPLE = 5;
	
    /**
     * A response tag to indicate a syntax error in the
     * corresponding prover call.  The {@code getInfo()} method should be
     * consulted for additional information.
     */
    public static final int SYNTAX_ERROR = 6;

    /**
     * A response tag to indicate that some progress
     * information is available from the prover.  Look in the {@link ProgressResponse}
     * class for additional information.
     */
    public static final int PROGRESS_INFORMATION = 7;

    /**
     * A response tag to indicate that the prover has timed
     * out on the corresponding prover call.  The {@code getInfo()} method 
     * should be consulted for additional information.
     */
    public static final int TIMEOUT = 8;

    /**
     * A response tag to indicate an inconsistency warning
     * from the prover for one or more of the previous {@link
     * SortedProver#declareAxiom(NodeBuilder.SPred)} and {@link
     * SortedProver#makeAssumption(NodeBuilder.SPred)} calls.  The {@code
     * getInfo()} method should be consulted for
     * additional information.
     */
    public static final int INCONSISTENCY_WARNING = 9;
    
    /**
     * Used by subclasses to figure out where to start counting for their
     * own `tags'.
     */
    protected static final int LAST = 10;
    
    private final Properties info = new Properties();
    private final int tag;
    
    //@ private invariant tag == COUNTER_EXAMPLE ==> this instanceof CounterExampleResponse;
    //@ private invariant tag == PROGRESS_INFORMATION ==> this instanceof ProgressResponse;

    /**
     * @return A set of properties.  Typically, this field is used to represent
     *   property/value pairs specific to reporting prover progress,
     *   state, resource utilization, etc.
     */
    /*@ pure @*/public Properties getInfo()
    {
    	return info;
    }
    
    /**
     * @return an integer describing the result
     */
    //@ ensures \result >= OK && \result < LAST; 
    /*@ pure @*/public int getTag()
    {
    	return tag;
    }
    
    /** 
     * Simple constuctor.
     * @param tag the response of the prover. 
     */
    // This excludes COUNTER_EXAMPLE and PROGRESS_INFORMATION that have their own subclasses.
    //@ requires tag == OK || tag == FAIL || tag == SYNTAX_ERROR || tag == YES || tag == NO || tag == TIMEOUT;   
    public SortedProverResponse(int tag)
    {
    	this.tag = tag;
    }
}
