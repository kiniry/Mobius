/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.Sort;

public class NullLiteral extends Term
{
	public NullLiteral() { }
	public Sort getSort() { return Lifter.sortRef; }
	public void infer(int pass) { }
	public STerm dump() { return dumpBuilder.buildNull(); }
}