/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.nodebuilder.members.QuantVar;
import mobius.sortedProver.nodebuilder.members.Sort;
import javafe.ast.GenericVarDecl;

public class QuantVariable
{
	public final GenericVarDecl var;
	public final String name;
	public final Sort type;
	
	public QuantVar qvar;
	
	public QuantVariable(GenericVarDecl v, String n)
	{
		var = v;
		name = n;
		type = Lifter.typeToSort(v.type);
	}
}