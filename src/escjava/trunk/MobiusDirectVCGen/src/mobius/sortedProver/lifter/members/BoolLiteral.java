/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.Sort;

public class BoolLiteral extends Term
{
	final public boolean value;
	public BoolLiteral(boolean v) {	value = v; }
	public Sort getSort() { return Lifter.sortBool; }
	public void infer(int pass) { }
	public STerm dump() { return dumpBuilder.buildBool(value); }
}