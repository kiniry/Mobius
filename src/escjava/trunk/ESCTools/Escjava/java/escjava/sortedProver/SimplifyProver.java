package escjava.sortedProver;

import java.util.Enumeration;
import java.util.Properties;

import javafe.util.Assert;
import javafe.util.Info;

import escjava.backpred.BackPred;
import escjava.prover.ProverResponse;
import escjava.prover.SExp;
import escjava.prover.SList;
import escjava.prover.Simplify;
import escjava.prover.SimplifyOutput;
import escjava.prover.SimplifyResult;
import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.SimplifyNodeBuilder.Sx;
import escjava.translate.VcToString;

public class SimplifyProver extends SortedProver
{
	SimplifyNodeBuilder nodeBuilder = new SimplifyNodeBuilder();
	Simplify simpl = new Simplify();
	int pushHeight;
	BackPred backPred = new BackPred();

	public EscNodeBuilder getNodeBuilder()
	{
		return nodeBuilder;
	}

	public ProverResponse startProver()
	{
		started = true;
		return ProverResponse.OK;
	}

	public ProverResponse setProverResourceFlags(Properties properties)
	{
		return ProverResponse.OK;
	}

	public ProverResponse sendBackgroundPredicate()
	{
		backgroundPredicateSent = true;
		backPred.genUnivBackPred(simpl.subProcessToStream());
		simpl.sendCommands("");
		return ProverResponse.OK;
	}

	public ProverResponse declareAxiom(SPred formula) 
	{
		Assert.notFalse(pushHeight == 0);
		simpl.sendCommand("(BG_PUSH\n" + formulaToString(formula) + "\n)");
		return ProverResponse.OK;
	}
	
	String formulaToString(SPred form)
	{
		Sx formula = (Sx)form;
		StringBuffer sb = new StringBuffer();
		formula.dump(0, sb);		
		return sb.toString();
	}

	public ProverResponse makeAssumption(SPred formula)
	{	
		pushHeight++;
		simpl.sendCommand("(BG_PUSH\n" + formulaToString(formula) + "\n)");
		return ProverResponse.OK;
	}

	public ProverResponse retractAssumption(int count)
	{
		Assert.notFalse(pushHeight >= count);
		pushHeight -= count;
		while (count-- > 0)
			simpl.sendCommand("(BG_POP)");
		return ProverResponse.OK;
	}
	
	String[] labels;

	public ProverResponse isValid(SPred formula, Properties properties)
	{
		labels = null;
	    simpl.startProve();
	    String form = formulaToString(formula);
	    if (Info.on)
	    	Info.out("[proving formula\n" + form + "]");
	    simpl.subProcessToStream().println(form);
        Enumeration en = simpl.streamProve();
        
        SimplifyOutput lastOut = null;        
        while (en.hasMoreElements()) {
        	lastOut = (SimplifyOutput) en.nextElement();
        	
        	if (lastOut.getKind() == SimplifyOutput.COUNTEREXAMPLE) {
        		SList labs = ((SimplifyResult)lastOut).getLabels();
        		if (labs != null) {
        			SExp[] lst = labs.toArray();
        			labels = new String[lst.length];
        			for (int i = 0; i < lst.length; ++i)
        				labels[i] = lst[i].toString();
        		}
        		
        		return ProverResponse.COUNTER_EXAMPLE;
        	}
        }
        
        if (lastOut != null && lastOut.getKind() == SimplifyOutput.VALID)
        	return ProverResponse.YES;
        
		return ProverResponse.NO;
	}

	public ProverResponse stopProver()
	{
		started = false;
		simpl.close();
		return ProverResponse.OK;
	}

	public String[] getLabels()
	{
		return labels;
	}
}
