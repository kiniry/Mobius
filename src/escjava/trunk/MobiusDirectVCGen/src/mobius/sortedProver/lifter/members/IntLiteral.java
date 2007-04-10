/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.Sort;

public class IntLiteral extends Term
{
	final public long value;
	public IntLiteral(long v) { value = v; }
	public Sort getSort() { return Lifter.sortInt; }
	public void infer(int pass) { }
	public void printTo(StringBuffer sb) { sb.append(value); }
	public STerm dump() { return dumpBuilder.buildInt(value); }
}