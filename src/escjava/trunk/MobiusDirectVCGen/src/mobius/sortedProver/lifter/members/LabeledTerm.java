/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.SPred;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.Sort;
import javafe.util.Assert;

public class LabeledTerm extends Term
{
	public final boolean positive;
	public final String label;
	public Term body;
	boolean dirty;
	boolean skipIt;
	
	public LabeledTerm(boolean pos, String l, Term b)
	{
		positive = pos;
		label = l;
		body = b;
	}
	
	public Sort getSort() { return body.getSort(); } 		
	public void infer(int pass) 
	{
		body.infer(pass);
		body = Lifter.toPred(body);
	}		
	
	public void printTo(StringBuffer sb)
	{
		if (!positive)
			sb.append("~");
		sb.append(label).append(": ");
		body.printTo(sb);
	}
	
	public STerm dump()
	{
		if (skipIt)
			return body.dump();
		else
			return dumpBuilder.buildLabel(positive, label, (SPred)body.dump());
	}
	
	public void enforceLabelSense(int sense)
	{
		Assert.notFalse(!dirty);
		dirty = true;
		if ((positive && sense > 0) || (!positive && sense < 0)) {}
		else {
			//ErrorSet.error("label: " + label + " used with wrong sense s="+sense);
			//ErrorSet.caution("change positive: " + positive + " into " + (sense < 0));
			skipIt = true;
		}
		body.enforceLabelSense(sense);
	}
}