///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: Jip
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package bPlugin;

import jack.util.Logger;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;

public class Jip {

    Process p;
    OutputStream os;
    InputStream is, er;

    String mth;
    boolean debug;
    boolean isLaunched;

    public Jip(String project, String name, boolean debug, String[] exec) {
	this.debug = debug;
	try {

	    p = Runtime.getRuntime().exec(exec);
	    os = p.getOutputStream();
            is = p.getInputStream();
	    er = p.getErrorStream();
	    String[] possibleres= {"\nNo current PO\n", 
				   "\nSomeone is modifying component " 
				   + name};
	    String res = sendCommand("op " + project + "\n" + "b " + name + "\n", possibleres);
	    if (res.indexOf("\nSomeone is modifying component") != -1)
		isLaunched = false;
	    else
		isLaunched = true;
	}
	catch (IOException e) {
	    Logger.err.println("Cannot execute Atelier B.");
	    System.exit(1);
	}
    }
    
    String sendCommand(String command, String[] response) {
	byte[] b;
	String res = "";

	try {
	    PrintStream f = new PrintStream(os);
	    f.print(command);
	    f.flush();
	    os.flush();
	    //	    f.close();
	    Logger.get().println("Command " + command + " sent");
	    
	    int i;
	    lab : do {
		while ((i = is.available()) == 0 &&
		       er.available() == 0) ;
		if (i != 0) {
		    b = new byte[i];
		    is.read(b, 0, i);
		    res += new String(b);
		     if (debug) Logger.get().println("AA : " + res);
		     for (int k=0;k < response.length; k++)
		    if (res.length() >= response[k].length()) {
			if (res.substring(res.length()-response[k].length(), 
					  res.length()).equals(response[k]))
			    break lab;
		    }
		}
		else {
		    b = new byte[i];
		    er.read(b, 0, i);
		    res += new String(b);
		    if (debug) Logger.get().println("BB : " + res);
		    System.exit(1);
		}
	    }
		  while (true);
	}
	catch (IOException e) {
	    Logger.err.println("Cannot read buffer.");
	    System.exit(1);
	}
	return res;
    }
    
    public boolean pr(String name, int po, String tactic) throws java.rmi.RemoteException {
	String[] possibleres= {"\nEnd\n"};
	sendCommand("go(" + name + "." + po + ")\n", possibleres);
	String rep = sendCommand(tactic + "\n", possibleres);
	boolean res = rep.indexOf("Proved saved ") != -1;
	sendCommand("sw\n", possibleres);
    return res;
    }

     public boolean fh(String name, int po, String hyp) throws java.rmi.RemoteException {
	String[] possibleres= {"\nEnd\n"};
	sendCommand("go(" + name + "." + po + ")\n", possibleres);
	sendCommand("dd\n", possibleres);
	sendCommand("fh(" + hyp + ")\n", possibleres);
	String rep = sendCommand("pr\n", possibleres);
	sendCommand("sw\n", possibleres);	
	return rep.indexOf("Proved saved ") != -1;
    }

    public boolean isProved(String name, int po) {
	String[] possibleres= {"\nEnd\n", "\nNo current PO\n"};
	String res = sendCommand("gs\n", possibleres);
	String sub1 = res.substring(res.indexOf(name), res.length());
	String sub2 = sub1.substring(sub1.indexOf("PO" + po)+("PO" + po).length()+1, 
				     sub1.indexOf("PO" + po)+("PO" + po).length()+2);
	return sub2.equals("P");
    }

    public void qu() {
	String[] possibleres = {"End of proof session\n"};
	sendCommand("qu\n", possibleres);
	String[] possibleres1 = {"\n"};
	sendCommand("q\n", possibleres1);
    }
}
