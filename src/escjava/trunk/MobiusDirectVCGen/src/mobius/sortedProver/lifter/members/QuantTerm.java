/**
 * 
 */
package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.SAny;
import mobius.sortedProver.NodeBuilder.SPred;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.QuantVar;
import mobius.sortedProver.nodebuilder.members.Sort;

public class QuantTerm extends Term
{
	public final boolean universal;
	public final QuantVariable[] vars;
	public final Term[][] pats;
	public final Term[] nopats;
	public Term body;
	
	public QuantTerm(boolean universal, QuantVariable[] vars, Term body, Term[][] pats, Term[] nopats)
	{
		this.universal = universal;
		this.vars = vars;
		this.body = body;
		this.pats = pats;
		this.nopats = nopats;		
	}
	
	public Sort getSort() { return Lifter.sortPred; } 		
	public void infer(int pass)		
	{			
		if (Lifter.doTrace)
			Lifter.trace("infer start q " + pass + ": " + this);
		body.infer(pass);
		body = Lifter.toPred(body);
		if (Lifter.doTrace)
			Lifter.trace("infer q " + pass + ": " + this);
	}
	
	public void printTo(StringBuffer sb)
	{
		sb.append("forall [");
		for (int i = 0; i < vars.length; ++i)
			sb.append(vars[i].name + ":" + vars[i].type + /*"/" + vars[i].var.type +*/ ", ");
		sb.append("] ");
		body.printTo(sb);
	}
	
	public STerm dump()
	{
		QuantVar[] qvars = new QuantVar[vars.length];
		QuantVar[] prev = new QuantVar[vars.length];
		for (int i = 0; i < vars.length; ++i) {
			prev[i] = vars[i].qvar;
			vars[i].qvar = dumpBuilder.registerQuantifiedVariable(vars[i].name, 
										Lifter.mapSortTo(dumpBuilder, vars[i].type));
			qvars[i] = vars[i].qvar;
		}
		SPred qbody = (SPred) body.dump();
		STerm[][] qpats = null;
		STerm[] qnopats = null;
		
		if (pats != null) {
			qpats = new SAny[pats.length][];
			for (int i = 0; i < pats.length; ++i)
				qpats[i] = Lifter.dumpTermArray(pats[i]);				
		}
		
		if (nopats != null) qnopats = Lifter.dumpTermArray(nopats);
		
		for (int i = 0; i < vars.length; ++i) {
			vars[i].qvar = prev[i];
		}
		
		if (universal)
			return dumpBuilder.buildForAll(qvars, qbody, qpats, qnopats);
		else if (qpats == null && qnopats == null)
			return dumpBuilder.buildExists(qvars, qbody);
		else
			return dumpBuilder.buildNot( 
					dumpBuilder.buildForAll(qvars,
							dumpBuilder.buildNot(qbody),
							qpats, qnopats));
	}
	
	public void enforceLabelSense(int sense)
	{
		body.enforceLabelSense(sense);
	}
}