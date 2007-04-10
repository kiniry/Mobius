/**
 * 
 */
package escjava.sortedProver.nodebuilder.members;


public class FnSymbol extends Symbol 
{
	public final Sort[] argumentTypes;
	public final Sort retType;
	
	public FnSymbol(String name, Sort[] args, Sort ret_type)
	{
		super(name);
		argumentTypes = args;
		retType = ret_type;
	}
	
	public String toString()
	{
		String s = name + " : (";
		for (int i = 0; i < argumentTypes.length; ++i) {
			if (i != 0) s += " * ";
			s += argumentTypes[i];
		}
		return s + ") -> " + retType;
	}
}