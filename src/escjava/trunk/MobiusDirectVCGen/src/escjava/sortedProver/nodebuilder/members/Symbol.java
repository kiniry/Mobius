/**
 * 
 */
package escjava.sortedProver.nodebuilder.members;

import escjava.sortedProver.NodeBuilder;

public class Symbol
{
	
	public final int id;
	public final String name;
	
	public Symbol(String name)
	{
		this.name = name;
		this.id = NodeBuilder.currentSymbol++;
		NodeBuilder.symbolsById.put(new Integer(id), this);
	}
	
	public String toString()
	{
		return name;
	}
}