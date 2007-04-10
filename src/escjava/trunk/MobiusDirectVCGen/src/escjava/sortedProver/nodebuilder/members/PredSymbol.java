/**
 * 
 */
package escjava.sortedProver.nodebuilder.members;

import escjava.sortedProver.NodeBuilder;


public class PredSymbol extends FnSymbol 
{ 
	public PredSymbol(String name, Sort[] args)
	{
		super(name, args, NodeBuilder.sortPred);
	}
}