/*
 * Created on Feb 23, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package bPlugin;

import jab.eJab;

import java.rmi.RemoteException;

/**
 *
 *  @author L. Burdy
 **/
public class Ab3_6 extends Ab {

	private String bbatchExe;
	private String ressourceAB;

	public Ab3_6(String bbatch, String ressource, String bdp) {
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
		return new Ab3_6(bbatchExe, ressourceAB, projectDir);
	}

}
