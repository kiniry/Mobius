package escjava.sortedProver.simplify;

import java.util.Enumeration;
import java.util.Properties;

import javafe.util.Assert;
import javafe.util.Info;

import escjava.backpred.BackPred;
import escjava.sortedProver.SortedProverResponse;
import escjava.prover.SExp;
import escjava.prover.SList;
import escjava.prover.Simplify;
import escjava.prover.SimplifyOutput;
import escjava.prover.SimplifyResult;
import escjava.sortedProver.CounterExampleResponse;
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.SortedProver;
import escjava.sortedProver.SortedProverCallback;
import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.simplify.SimplifyNodeBuilder.Sx;
import escjava.translate.VcToString;

/*@ non_null_by_default @*/
public class SimplifyProver extends SortedProver
{
	SimplifyNodeBuilder nodeBuilder = new SimplifyNodeBuilder();
	Simplify simpl = new Simplify();
	int pushHeight;
	BackPred backPred = new BackPred();
	
	SortedProverResponse ok = new SortedProverResponse(SortedProverResponse.OK);

	public EscNodeBuilder getNodeBuilder()
	{
		return nodeBuilder;
	}

	public SortedProverResponse startProver()
	{
		started = true;
		return ok;
	}

	public SortedProverResponse setProverResourceFlags(Properties properties)
	{
		return ok;
	}

	public SortedProverResponse sendBackgroundPredicate()
	{
		backgroundPredicateSent = true;
		backPred.genUnivBackPred(simpl.subProcessToStream());
		simpl.sendCommands("");
		return ok;
	}

	public SortedProverResponse declareAxiom(SPred formula) 
	{
		Assert.notFalse(pushHeight == 0);
		simpl.sendCommand("(BG_PUSH\n" + formulaToString(formula) + "\n)");
		return ok;
	}
	
	String formulaToString(SPred form)
	{
		Sx formula = (Sx)form;
		StringBuffer sb = new StringBuffer();
		formula.dump(0, sb);		
		return sb.toString();
	}

	public SortedProverResponse makeAssumption(SPred formula)
	{	
		pushHeight++;
		simpl.sendCommand("(BG_PUSH\n" + formulaToString(formula) + "\n)");
		return ok;
	}

	public SortedProverResponse retractAssumption(int count)
	{
		Assert.notFalse(pushHeight >= count);
		pushHeight -= count;
		while (count-- > 0)
			simpl.sendCommand("(BG_POP)");
		return ok;
	}
	
	public SortedProverResponse isValid(SPred formula, SortedProverCallback callback, Properties properties)
	{
	    simpl.startProve();
	    String form = formulaToString(formula);
	    if (Info.on)
	    	Info.out("[proving formula\n" + form + "]");
	    simpl.subProcessToStream().println(form);
        Enumeration en = simpl.streamProve();
        int cc = 0;
        
        SimplifyOutput lastOut = null; 
        while (en.hasMoreElements()) {
        	lastOut = (SimplifyOutput) en.nextElement();
        	
        	if (lastOut.getKind() == SimplifyOutput.COUNTEREXAMPLE) {
        		SList labs = ((SimplifyResult)lastOut).getLabels();
        		if (labs != null) {
        			SExp[] lst = labs.toArray();
        			String[] labels = new String[lst.length];
        			for (int i = 0; i < lst.length; ++i)
        				labels[i] = lst[i].toString();
        			callback.processResponse(new CounterExampleResponse(labels));        			
        			// we ignore any possible discharge hint called on the response
        		}
        	}
        }
        
        if (lastOut != null && lastOut.getKind() == SimplifyOutput.VALID)
        	return new SortedProverResponse(SortedProverResponse.YES);
        
		return new SortedProverResponse(SortedProverResponse.NO);
	}

	public SortedProverResponse stopProver()
	{
		started = false;
		simpl.close();
		return ok;
	}
}
