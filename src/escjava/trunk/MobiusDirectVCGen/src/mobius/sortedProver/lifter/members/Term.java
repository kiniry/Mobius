/**
 * 
 */
package mobius.sortedProver.lifter.members;

import java.util.Iterator;
import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.Variable;
import mobius.sortedProver.EscNodeBuilder;
import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.SAny;
import mobius.sortedProver.NodeBuilder.SBool;
import mobius.sortedProver.NodeBuilder.SInt;
import mobius.sortedProver.NodeBuilder.SPred;
import mobius.sortedProver.NodeBuilder.SReal;
import mobius.sortedProver.NodeBuilder.SRef;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.NodeBuilder.SValue;
import mobius.sortedProver.nodebuilder.members.Sort;
import javafe.util.Assert;

public abstract class Term
{	/*@ nullable @*/EscNodeBuilder dumpBuilder;
	abstract public Sort getSort();
	abstract public void infer(int pass);
	
	public void printTo(StringBuffer sb)
	{
		sb.append(super.toString());		
	}
	
	public String toString()
	{
		StringBuffer sb = new StringBuffer();
		printTo(sb);
		return sb.toString();
	}
	
	abstract public STerm dump();
	
	public SPred dumpPred()
	{	
		//ErrorSet.caution("( dumpPred");
		Assert.notFalse(Lifter.follow(getSort()) == Lifter.sortPred);
		SPred p = (SPred)dump();
		//ErrorSet.caution(" dumpPred )");
		return p;
	}
	
	public SAny dumpAny()
	{
		Assert.notFalse(Lifter.follow(getSort()) != Lifter.sortPred);
		return (SAny)dump();
	}
	
	public SValue dumpValue()
	{
		Assert.notFalse(getSort().isSubSortOf(Lifter.sortValue));
		return (SValue)dump();
	}
	
	public SInt dumpInt()
	{
		Assert.notFalse(getSort().isSubSortOf(Lifter.sortInt));
		return (SInt)dump();
	}
	
	public SBool dumpBool()
	{
		Assert.notFalse(getSort().isSubSortOf(Lifter.sortBool));
		return (SBool)dump();
	}
	
	public SReal dumpReal()
	{
		Assert.notFalse(getSort().isSubSortOf(Lifter.sortReal));
		return (SReal)dump();
	}
	
	public SRef dumpRef()
	{
		Assert.notFalse(getSort().isSubSortOf(Lifter.sortRef));
		return (SRef)dump();
	}
	
	public void enforceLabelSense(int sense)
	{			
	}
	//public abstract Term subst();
}