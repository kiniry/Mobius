/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.Sort;

public class QuantVariableRef extends Term
{
	final public QuantVariable qvar;
	
	public QuantVariableRef(QuantVariable q) { qvar = q; }		
	public Sort getSort() { return qvar.type; }
	public void infer(int pass) { }
	
	public void printTo(StringBuffer sb)
	{
		sb.append("?" + qvar.name + ":" + qvar.type);
	}
	
	public STerm dump()
	{
		return dumpBuilder.buildQVarRef(qvar.qvar); 
	}

}