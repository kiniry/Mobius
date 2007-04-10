/**
 * 
 */
package mobius.sortedProver.nodebuilder.members;

import mobius.sortedProver.NodeBuilder;


public class PredSymbol extends FnSymbol 
{ 
	public PredSymbol(String name, Sort[] args)
	{
		super(name, args, NodeBuilder.sortPred);
	}
}