package mobius.sortedProver;

import mobius.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.SortedProverResponse;

public interface SortedProverCallback
{
	/**
	 * Called when the prover finds a counter example, wants to inform about progress,
	 * error or other condition.
	 * 
	 * @param resp is the response to be processed, some responses provide methods to
	 * return information to the prover
	 */
	void processResponse(SortedProverResponse resp);
}
