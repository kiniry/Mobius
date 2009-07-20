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
public class Ab3_5 extends Ab {

	private String bbatchExe;
	private String ressourceAB;
	private String abDef;
	
	public Ab3_5(String bbatch, String ressource, String abDef, String bdp) {
		bbatchExe = bbatch;
		ressourceAB = ressource;
		this.abDef = abDef;
		projectDir = bdp;
		   exec = new String[3];
		    exec[0] = bbatch;
		    exec[1] = "-a=" + ressourceAB;
		    exec[2] = "-d=" + abDef;
		    printingProjectList = "Printing Projects list ...";
		    interpretationAborted = "Interpretation aborted in line ";
	}
	
	public eJab getNewAb() throws RemoteException {
		return new Ab3_5(bbatchExe, ressourceAB, abDef, projectDir);
	}

}
