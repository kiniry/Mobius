/*
 * Created on Feb 23, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package bPlugin;

import jab.eJab;
import jack.util.Logger;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.rmi.RemoteException;
import java.util.Enumeration;
import java.util.Vector;

/**
 *
 *  @author L. Burdy
 **/
public class AbB4Free2_0 extends Ab {

	private String bbatchExe;
	private String ressourceAB;

	public AbB4Free2_0(String bbatch, String ressource, String bdp) {
		bbatchExe = bbatch;
		ressourceAB = ressource;
		projectDir = bdp;
		 exec = new String[2];
	    exec[0] = bbatch;
	    exec[1] = "-r=" + ressourceAB;
	    printingProjectList = "Printing Project list ...";
	    interpretationAborted = "Interpretation aborted at line ";
	}
	
	public eJab getNewAb() throws RemoteException {
		return new AbB4Free2_0(bbatchExe, ressourceAB, projectDir);
	}
	public String[] getProjectList() throws RemoteException {
        Vector projectList = new Vector();
        String res = sendCommand("spl\n"); 
	
	int i = res.indexOf(printingProjectList) 
	    + printingProjectList.length() + 1;
        while (i+1 < res.length()) {
	    Logger.get().println("--> " + res.substring(i, res.length()));
	    projectList.add(res.substring(i, i = res.indexOf('\n', i+1)));
	}
        String[] result = new String[projectList.size()-6];
	Enumeration e = projectList.elements();
	for (i = 0; i < projectList.size()-6; i++) {
	    result[i] = ((String) e.nextElement()).substring(7);	
	}
	return result;
	}
	/* (non-Javadoc)
	 * @see jab.eJab#addFile(java.lang.String, java.lang.String)
	 */
	public boolean addFile(String project, String name) throws RemoteException {
		try {
		    PrintStream ps = 
			new PrintStream(new FileOutputStream(new File(directory 
								      + "/" 
								      + name 
								      + ".mch")));
		    ps.println("MACHINE");
		    ps.println("   " + name);
		    ps.println("END");
		    ps.close();
		}
		catch (IOException ie) {
		    throw new RemoteException("Cannot create " 
				       + directory
				       + "/" 
				       + name 
				       + ".mch");
		}
		this.name = name;
		sendCommand("cd " + directory + "\n"
			    + "op " + project + "\n"
			    + "add_file " + name + ".mch\n"
			    + "t " + name + "\n"
			    + "po " + name + " 1\n");
		return true;
	}
	
	void proofCounter(String tmp, String res) {
		for (int k = 0; k < tmp.length(); k++) {
			if (tmp.substring(k).startsWith("Proved\nPRV##"))
				cptProvedRunning++;			
			if (tmp.substring(k).startsWith("Unproved\nPRV##"))
				cptUnprovedRunning++;
		}
		/*krtpid*/
		if (pid == null
				&& res.indexOf('\n', 35) >= 35 
				&& res.substring(29, 
						35).equals("krtpid")) {
			pid = res.substring(35, 
					res.indexOf('\n', 35));
		}
	}
	
	
}
