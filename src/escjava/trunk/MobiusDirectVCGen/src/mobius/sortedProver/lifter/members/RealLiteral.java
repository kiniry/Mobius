/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.Sort;

public class RealLiteral extends Term
{
	final public double value;
	public RealLiteral(double v) { value = v; }
	public Sort getSort() { return Lifter.sortReal; } 
	public void infer(int pass) { }
	public STerm dump() { return dumpBuilder.buildReal(value); }
}