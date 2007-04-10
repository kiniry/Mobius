/**
 * 
 */
package mobius.sortedProver.nodebuilder.members;


public class QuantVar extends Symbol 
{
	public final Sort type;
	public QuantVar(String name, Sort type)
	{
		super(name);
		this.type = type;
	}
	
	public String toString()
	{
		return "?" + name + " : " + type;
	}
}