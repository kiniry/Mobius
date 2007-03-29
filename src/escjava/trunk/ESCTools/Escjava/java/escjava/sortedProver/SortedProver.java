package escjava.sortedProver;

import java.util.Properties;
import escjava.prover.ProverResponse;
import escjava.sortedProver.NodeBuilder.SPred;

/*@ non_null_by_default @*/
public abstract class SortedProver
{
    /*
     * Variables indicating the state of the prover
     */
    public boolean started = false ;
    public boolean backgroundPredicateSent = false;

    /**
     * Get the {@link NodeBuilder} object that can be used to construct
     * formulas for the current prover.
     *
     * @return a {@link NodeBuilder} object for the current prover.
     */
    public abstract EscNodeBuilder getNodeBuilder();

    /**
     * Start up the prover.  After the prover is started correctly it
     * should be ready to receive any of the commands embodied by all
     * the other methods of this API.
     *
     * @return a response code.  A response code of {@link
     * ProverResponse#OK} indicates that the prover started successfully
     * and is ready to receive commands.  A response code of {@link
     * ProverResponse#FAIL} indicates that the prover did not start
     * successfully and is not ready to receive commands.  In the latter
     * case, {@link ProverResponse.FAIL.info} can contain additional
     * arbitrary information about the failure.
     */

    /*@ public normal_behavior
      @   assignable started;
      @   ensures \result == ProverResponse.OK ||
      @           \result == ProverResponse.FAIL;
      @   ensures started;
      @*/

    public abstract ProverResponse startProver();

    /**
     * Send arbitrary information to the prover.  Typically this
     * information is not mandatory and is only suggestions or
     * informative information from the front-end.  This data is highly
     * prover-dependent.
     *
     * @param properties the set of property/value pairs to send to the
     * prover.
     * @return a response code.
     */
    /*@   requires started;
      @   ensures \result == ProverResponse.OK || 
      @           \result == ProverResponse.FAIL ||
      @           \result == ProverResponse.SYNTAX_ERROR ||
      @           \result == ProverResponse.PROGRESS_INFORMATION;
      @*/

    public abstract ProverResponse setProverResourceFlags(Properties properties);

    /**
     * Send the theory background predicate to the solver.
     *
     * @return a response code.
     */
    /*@   requires started;
      @   requires !backgroundPredicateSent;
      @   ensures \result == ProverResponse.OK || 
      @           \result == ProverResponse.FAIL ||
      @           \result == ProverResponse.SYNTAX_ERROR ||
      @           \result == ProverResponse.INCONSISTENCY_WARNING;
      @   ensures backgroundPredicateSent;
      @*/
    
    public abstract ProverResponse sendBackgroundPredicate();

    /**
     * Declare a new axiom in the current theory.
     *
     * @param formula
     * @return a response code.
     */
    /*@   requires started;
      @   ensures \result == ProverResponse.OK || 
      @           \result == ProverResponse.FAIL ||
      @           \result == ProverResponse.SYNTAX_ERROR ||
      @           \result == ProverResponse.INCONSISTENCY_WARNING;
      @*/

    public abstract ProverResponse declareAxiom(SPred formula);

    /**
     * Make an assumption.
     *
     * @param formula the assumption to make.
     * @return a response code.
     */
    /*@   requires started;
      @   ensures \result == ProverResponse.OK || 
      @           \result == ProverResponse.FAIL ||
      @           \result == ProverResponse.SYNTAX_ERROR ||
      @           \result == ProverResponse.INCONSISTENCY_WARNING;
      @*/

    public abstract /*@ non_null @*/ ProverResponse makeAssumption(/*@ non_null @*/ SPred formula);

    /**
     * Retract some assumptions.
     *
     * @param count the number of assumptions to retract.
     * @return a response code.
     */
    /*@   requires started;
      @   requires count >= 0 ;
      @   ensures \result == ProverResponse.OK ||
      @           \result == ProverResponse.FAIL;
      @*/

    public abstract ProverResponse retractAssumption(int count);

    /**
     * Check the validity of the given formula given the current theory,
     * its axioms, and the current set of assumptions.
     *
     * @param formula the formula to check.
     * @param callback the callbacks that will be called during the search
     * @param properties a set of hints, primarily resource bounds on
     * this validity check.
     * @return a response code.
     */
    /*@   requires started;
      @   ensures \result == ProverResponse.YES ||
      @           \result == ProverResponse.NO ||
      @           \result == ProverResponse.SYNTAX_ERROR ||
      @           \result == ProverResponse.TIMEOUT ||
      @           \result == ProverResponse.FAIL;
      @*/

    public abstract ProverResponse isValid(
    		     SPred formula,
    			 SortedProverCallback callback,
    			 Properties properties);
    
    /**
     * Stop the prover.
     *
     * @return a response code.
     */
    /*@ public normal_behavior
      @   requires started;
      @   assignable started;
      @   ensures \result == ProverResponse.OK ||
      @           \result == ProverResponse.FAIL;
      @   ensures started == false;
      @*/

    public abstract ProverResponse stopProver();
}
