package escjava.sortedProver;

import escjava.sortedProver.NodeBuilder.SPred;

public interface SortedProverCallback
{
	/**
	 * Called when the prover finds a counter example.
	 * 
	 * @param labels the current set of labels describing the counter example
	 * @return The client can return here a formula that would be conjoined to
	 * the original query to hint the direction in which 
	 * prover should look for further counter examples or null to indicate no such 
	 * hint.  The prover can treat the formula returned as a theory tautology (in
	 * which case it can say the formula is valid).  It is however free to ignore that.
	 */
	SPred counterExample(String[] labels);
	
	/**
	 * Called by prover from time to time.  The parameters are by no means accurate.
	 * 
	 * @param progress should be number of things done (for example conflicts found)
	 * @param eta should be the estimated total number of things done
	 * @return The client should return false to tell the prover to stop trying
	 * or true to go further.
	 */
	boolean progressIndication(int progress, int eta);
}
