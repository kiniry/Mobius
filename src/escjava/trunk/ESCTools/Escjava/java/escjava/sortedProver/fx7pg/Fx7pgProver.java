package escjava.sortedProver.fx7pg;

import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.Properties;

import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.FatalError;
import javafe.util.Info;
import escjava.backpred.BackPred;
import escjava.prover.SubProcess;
import escjava.sortedProver.CounterExampleResponse;
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.SortedProverCallback;
import escjava.sortedProver.SortedProverResponse;
import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.auflia.AufliaProver;
import escjava.sortedProver.fx7.Fx7NodeBuilder;
import escjava.sortedProver.simplify.SimplifyNodeBuilder.Sx;

public class Fx7pgProver extends AufliaProver
{
	Process fx7;	

	String readLine()
	{
		try {
			InputStream s = fx7.getInputStream();
			
			int c =s.read();
			while (c == ' ' || c == '\n' || c == '\r')
				c = s.read();
			if (c < 0) return "EOF";
			
			StringBuffer sb = new StringBuffer();
			sb.append((char)c);
			for (;;) {
				c = s.read();
				if (c == '\n' || c == '\r' || c < 0) break;
				sb.append((char)c);
			}
			
			String line = sb.toString();
			if (Info.on)
				Info.out("fx7: " + line);
			return line;
		} catch (IOException x) {
			ErrorSet.fatal(x.toString());
			return null; // unreached
		}
	}
	
	static final int INFO = 0;
	static final int WARN = 1;
	static final int ANSWER = 2;
	static final int ERROR = 3;
	static final int EOF = 4;
	
	int severity(String msg)
	{
		if (msg.startsWith("TEMP:") || msg.startsWith("INFO:") || msg.startsWith("GRIND:"))
			return INFO;
		else if (msg.startsWith("WARN:"))
			return WARN;
		else if (msg.startsWith("ANSWER:"))
			return ANSWER;
		else if (msg == "EOF")
			return EOF;
		else
			return ERROR;
	}
	
	String readLine(int severity)
	{
		String l;
		
		do {
			l = readLine();
		} while (severity(l) < severity);
		
		return l; 
	}
	
	public SortedProverResponse isValid(SPred formula, SortedProverCallback callback, Properties properties)
	{
		Properties propsNow = new Properties();
		propsNow.putAll(currentProperties);
		propsNow.putAll(properties);
		
		String filename = encodeProblemName(properties);
		filename += ".smt";
		
		Enumeration e = propsNow.keys();
		String opts = "-o:ProofLogging=1,ProofFile=" + filename + ".rw";
		while (e.hasMoreElements()) {			
			String key = (String)e.nextElement();
			if (key.equals("ProblemName"))
				continue;
			opts += "," + key + "=" + properties.getProperty(key);
		}
		
		saveQuery(filename, formula);
		
		String args[] = new String[] { "fx7", "-mechanical", "-t:60", opts, filename};
		
		try {			
			fx7 = Runtime.getRuntime().exec(args,null);
		} catch (IOException x) {
			ErrorSet.fatal(x.toString());
		}		
		
		Info.out("invoking fx7 on : " + filename + ", with " + opts);
		
		String ans = readLine(ANSWER);
		try {
			if (ans.startsWith("ANSWER: SAT")) {
				ans = readLine(INFO);
				if (ans.startsWith("INFO: labels: ")) {
					ans = ans.substring(14);
					String[] labels = ans.split(" ");
					for (int i = 0; i < labels.length; ++i) {
						String lab = nodeBuilder.errVarToLabel(labels[i]);
						if (lab != null)
							labels[i] = lab;
					}
					callback.processResponse(new CounterExampleResponse(labels));
				} else {
					// It happens if there were no labels in the query.
					// ErrorSet.fatal("no labels, no donut: " + ans);
				}
				
				return new SortedProverResponse(SortedProverResponse.NO);
			} else if (ans.startsWith("ANSWER: UNSAT")) {
				return new SortedProverResponse(SortedProverResponse.YES);
			} else if (ans.startsWith("ANSWER: TIMEOUT")) {
				return new SortedProverResponse(SortedProverResponse.TIMEOUT);
			} else {	    		    	
				ErrorSet.fatal("got some evil response from fx7: " + ans);
				return new SortedProverResponse(SortedProverResponse.FAIL);
			}
		} finally {
			fx7.destroy();
			fx7 = null;
		}
	}
}
