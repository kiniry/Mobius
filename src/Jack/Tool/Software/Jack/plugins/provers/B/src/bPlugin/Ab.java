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
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InterruptedIOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.rmi.RemoteException;
import java.util.Enumeration;
import java.util.Vector;

/**
 *
 *  @author L. Burdy
 **/
public abstract class Ab implements eJab {

	
	protected String[] exec;
	protected String printingProjectList;
	protected String interpretationAborted;
	protected String projectDir;
	
	
    Process atelierb;
    String pid;
    boolean proofRunning;
    int cptProvedRunning;
    int cptUnprovedRunning;
    String directory;
    String name;
    FileOutputStream fos;
    FileInputStream fis;
    int available;
    ProveThread proveThread;
    Jip jip;
    

//	/**
//	 * @param bbatch
//	 * @param ressource
//	 */
//	public Ab(String bbatch, String ressource, String version) {
//		bbatchExe = bbatch;
//		ressourceAB = ressource;
//		if (version.equals("3.6")) {
//		    exec = new String[2];
//	    exec[0] = bbatch;
//	    exec[1] = "-r=" + ressourceAB;
//	    printingProjectList = "Printing Project list ...";
//	    interpretationAborted = "Interpretation aborted at line ";
//	}
//	else {
//	    exec = new String[3];
//	    exec[0] = bbatch;
//	    exec[1] = "-a=" + AB;
//	    exec[2] = "-d=" + ab_def;
//	    printingProjectList = "Printing Projects list ...";
//	    interpretationAborted = "Interpretation aborted in line ";
//	}
//
//	}

	/* (non-Javadoc)
	 * @see jab.eJab#getNewAb()
	 */
	public abstract eJab getNewAb() throws RemoteException;

	/* (non-Javadoc)
	 * @see jab.eJab#initialize(boolean)
	 */
	public void initialize(boolean debug) throws RemoteException {
       sendCommand("");
 	}

	/* (non-Javadoc)
	 * @see jab.eJab#checkProject(java.lang.String)
	 */
	public boolean checkProject(String project) throws RemoteException {
		return (directory = getDirectory(project)) != null;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#newProject(java.lang.String)
	 */
	public void newProject(String project) throws RemoteException {
		File f = new File(projectDir + File.separatorChar + project);
		if (!f.exists())
		    f.mkdir();
		f = new File(projectDir + File.separatorChar + project + "/bdp");
		if (!f.exists())
		    f.mkdir();
		f = new File(projectDir + File.separatorChar + project + "/lang");
		if (!f.exists())
		    f.mkdir();
		String res = sendCommand("crp " 
					 + project 
					 + " " 
					 + projectDir 
					 + File.separatorChar 
					 + project 
					 + "/bdp " 
					 + projectDir
					 + File.separatorChar 
					 + project 
					 + "/lang\n");
		
		throw new RemoteException(res);
	}

	/* (non-Javadoc)
	 * @see jab.eJab#removeProject(java.lang.String)
	 */
	public String removeProject(String project) throws RemoteException {
		sendCommand("rp " + project + "\n");
        return "";
	}

	/* (non-Javadoc)
	 * @see jab.eJab#getProjectList()
	 */
	public String[] getProjectList() throws RemoteException {
        Vector projectList = new Vector();
        String res = sendCommand("spl\n"); 
	
	int i = res.indexOf(printingProjectList) 
	    + printingProjectList.length() + 1;
        while (i+1 < res.length()) {
	    Logger.get().println("--> " + res.substring(i+7, res.length()));
	    projectList.add(res.substring(i+7, i = res.indexOf('\n', i+7)));
	}
        String[] result = new String[projectList.size()-2];
	Enumeration e = projectList.elements();
	for (i = 0; i < projectList.size()-2; i++) {
	    result[i] = (String) e.nextElement();	
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
			    + "po " + name + "\n");
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#openPo(java.lang.String)
	 */
	public boolean openPo(String project) throws RemoteException {
		try {
		    fos = new FileOutputStream(new File(directory 
							+ "/" 
							+ name 
							+ ".po"));
		}
		catch (IOException ioe) {
		    throw new RemoteException("Open Po", ioe);
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#openPmi(java.lang.String, java.lang.String)
	 */
	public boolean openPmi(String name, String project) throws RemoteException {
		Logger.get().println("Opening " + directory 
						   + "/" 
						   + name 
						   + ".pmi");
				try {
				    fos = new FileOutputStream(new File(directory 
									+ "/" 
									+ name 
									+ ".pmi"));
				}
				catch (IOException ioe) {
				    throw new RemoteException("Open Pmi", ioe);
				}
				return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#send(byte[])
	 */
	public boolean send(byte[] data) throws RemoteException {
		try {
		    fos.write(data);
		}
		catch (IOException ioe) {
		    throw new RemoteException("Send", ioe);
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#closePo()
	 */
	public boolean closePo() throws RemoteException {
		try {
		    fos.close();
		}
		catch (IOException ioe) {
		    throw new RemoteException("close Po", ioe);
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#closePmi()
	 */
	public boolean closePmi() throws RemoteException {
		try {
		    fos.close();
		}
		catch (IOException ioe) {
		    throw new RemoteException("close Pmi", ioe);
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#beginReadPmi(java.lang.String, java.lang.String)
	 */
	public boolean beginReadPmi(String project, String name) throws RemoteException {
		try {
		    fis = new FileInputStream(new File(getDirectory(project) 
						       + "/" 
						       + name 
						       + ".pmi"));
		}
		catch (IOException ioe) {
		    throw new RemoteException("beginning read Pmi", ioe);
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#isPmiAvailable()
	 */
	public boolean isPmiAvailable() throws RemoteException {
		try {
		    return (available = fis.available()) != 0;
		}
		catch  (IOException ioe) {
		    throw new RemoteException("Check if Pmi is available", ioe);
		}
	}

	/* (non-Javadoc)
	 * @see jab.eJab#read()
	 */
	public byte[] read() throws RemoteException {
		try {
		    byte[] tmp = new byte[available];
		    fis.read(tmp, 0, available);
		    return tmp;
		}
		catch  (IOException ioe) {
		    throw new RemoteException("Read", ioe);
		}
	}

	/* (non-Javadoc)
	 * @see jab.eJab#endReadPmi()
	 */
	public boolean endReadPmi() throws RemoteException {
		try {
		    fis.close();
		}
		catch  (IOException ioe) {
		    throw new RemoteException("End reading Pmi", ioe);
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#prove(java.lang.String, java.lang.String, int)
	 */
	public void prove(String project, String name, int force) throws RemoteException {
		cptProvedRunning = 0;
		cptUnprovedRunning = 0;
		proofRunning = true;
		proveThread = new ProveThread(this, project, name, force);
		proveThread.start();
		RemoteException re = proveThread.getRemoteExc();
		if (re != null)
		    throw re;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#getProofRunning()
	 */
	public boolean getProofRunning() throws RemoteException {
		if (!proofRunning) {
		    Logger.get().println(toString() + " proof no longer running.");
		}
		return proofRunning;
	 	}

	/* (non-Javadoc)
	 * @see jab.eJab#getCptProvedRunning()
	 */
	public int getCptProvedRunning() throws RemoteException {
		return cptProvedRunning;
    }
    
    public int getCptUnprovedRunning() {
	return cptUnprovedRunning;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#killProofProcess()
	 */
	public void killProofProcess() throws RemoteException {
		if (pid != null) {
		    String exec[] = {"/bin/kill",
				     "-13",
				     pid};
		    try {
		    Runtime.getRuntime().exec(exec);
		    }
		    catch (IOException ioe) {
			throw new RemoteException("kill -9 " + pid, ioe);
		    }
		}
		if (atelierb != null) {
		    Logger.get().println("Kill proof process. " + atelierb.toString());
		    atelierb.destroy();
		}
		if (proveThread != null)
		    proveThread.interrupt();
	}

	/* (non-Javadoc)
	 * @see jab.eJab#browse(java.lang.String, java.lang.String)
	 */
	public boolean browse(String project, String name) throws RemoteException {
		jip = new Jip(project, name, false, exec);
		return jip.isLaunched;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#isProved(java.lang.String, int)
	 */
	public boolean isProved(String name, int po) throws RemoteException {
		return jip.isProved(name, po);
	}

	/* (non-Javadoc)
	 * @see jab.eJab#getStatus(java.lang.String, java.lang.String, int)
	 */
	public boolean[] getStatus(String project, String name, int nbPo) throws RemoteException {
		String rep = sendCommand("op " + project + "\n"
								 + "b " + name + "\n"
								 + "gs\n"
								 + "qu\n");
					boolean[] res = new boolean[nbPo];
					int current = 0;
					for (int i=0; i < nbPo; i++) {
					    int tmp = rep.indexOf("      PO", current);
					    current = rep.indexOf(" ", tmp+7);
					    res[i] = rep.charAt(current+1) == 'P';
					}
					return res;
	}

	/* (non-Javadoc)
	 * @see jab.eJab#pr(java.lang.String, int, java.lang.String)
	 */
	public boolean pr(String name, int po, String tactic) throws RemoteException {
		return jip.pr(name, po, tactic);
	}

	/* (non-Javadoc)
	 * @see jab.eJab#fh(java.lang.String, int, java.lang.String)
	 */
	public boolean fh(String name, int po, String hyp) throws RemoteException {
		return jip.fh(name, po, hyp);
	}

	/* (non-Javadoc)
	 * @see jab.eJab#quitinteractiveprover()
	 */
	public void quitinteractiveprover() throws RemoteException {
		jip.qu();
	}

	/* (non-Javadoc)
	 * @see jab.eJab#q()
	 */
	public void q() throws RemoteException {
		sendCommand("q\n");
	}
	
    String sendCommand(String command) throws java.rmi.RemoteException {
    	byte[] b;
    	String res = "";
    	OutputStream os = null;
    	InputStream is = null, er = null;
    	FileOutputStream log = null;
    	
    	try {
    	    atelierb = Runtime.getRuntime().exec(exec);
    	    os = atelierb.getOutputStream();
                is = atelierb.getInputStream();
    	    er = atelierb.getErrorStream();

   	}
    	catch (IOException e) {
    	    throw new RemoteException("Cannot execute Atelier B. ", e);
    	}
    	
    	int j = 0;
    	
    	try {
    	    j = er.available();
    	}
    	catch (IOException e) {
    	    throw new RemoteException("Cannot read buffer. ", e);
    	}
    	
    	if (j != 0) {
    	    b = new byte[j];
    	    try {
    		er.read(b, 0, j);
    	    }
    	    catch (IOException e) {
    		throw new RemoteException("Cannot read buffer. ", e);
    	    }
    	    throw new RemoteException(new String(b));
    	}
    	
    	try {
    	    PrintStream f = new PrintStream(os);
    	    f.println(command);
    	    f.println("q");
    	    f.flush();
    	    os.flush();
    	    f.close();
    	    Logger.get().println("Command " + command + "\nq\n" + " sent");
    	    
    	    Object sync = new Object();
    	    
    	    Reader inReader = new Reader(this, sync, is);
    	    Reader errReader = new Reader(this, sync, er);

    	    pid = null;
    	    
    	    try {
    		
    		inReader.start();
    		errReader.start();
    		
    		lab : do {
    		    synchronized(sync) {
    			sync.notifyAll();
    		    }
    		    synchronized(this) {
    			while ((!errReader.isNotifier()) &&
    			       (!inReader.isNotifier())) {
    			    this.wait(5000);
    			}
    		    }
    		    if (errReader.isNotifier()) {
    			byte[] bb =  errReader.read();
    			if (log != null) log.write(bb);
    			throw new RemoteException(new String(bb));
    		    }
    		    else {
    			byte[] bb =  inReader.read();
    			if (log != null) log.write(bb);
    			String tmp = new String(bb);
    			res += tmp;
    			if (proofRunning)
    			    {
    				proofCounter(tmp,res);
    			    }
    			
    			if (res.length() >= 33 && 
    			    res.substring(res.length()-33, 
    					  res.length()-2).equals(interpretationAborted)) {
    			    break lab;
    			}
    			if (res.length() >= 32 && 
    			    res.substring(res.length()-32, 
    					  res.length()-11).equals("End of interpretation"))
    			    break lab;
    			inReader.notify = false;
    		    }
    		}
    		      while (true);
    	    }
    	    finally {
    		inReader.interrupt();
    		errReader.interrupt();
    		if (log != null) log.close();
    		atelierb = null;
    	    }
    	}
    	catch (IOException e) {
    	    throw new RemoteException("Cannot read buffer. ", e);
    	}
    	catch (InterruptedException ie) {
    	    throw new RemoteException("Thread has been interrupted ", ie);
    	}
    	return res;
        }

    private String getDirectory(String project) throws java.rmi.RemoteException {
        String res = sendCommand("infos_project " + project + "\n");
	int i = res.indexOf("Database path :");
	if (i != -1)
	    return res.substring(i+16, res.indexOf('\n', i));
	else
	    return null;
    }
    
    void proofCounter(String tmp, String res) {
    	for (int k = 0; k < tmp.length(); k++) {
    		if (tmp.charAt(k) == '+')
    			cptProvedRunning++;
    		if (tmp.charAt(k) == '-')
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


class Reader extends Thread {
    
    Object sync1;
    Object sync2;
    InputStream is;
    byte[] b;
    IOException ie;
    boolean notify;
    int length;
    
    Reader(Object synch1, Object synch2, InputStream i) {
	sync1 = synch1;
	sync2 = synch2;
	is = i;
    }
    
    public void run() {
	while (true) {
	    ie = null;
	    try {
		int i = is.read();
		if (i != -1) {
		    int j = is.available();
		    b = new byte[j + 1];
		    b[0] = (byte) i;
		    if (j != 0)
			is.read(b, 1, j);
		}
		else {
		    return;
		}
		notify = true;
		synchronized(sync1) {
		    sync1.notify();
		}
		synchronized(sync2) {
		    while (notify)
		    sync2.wait(2000);
		}
	    }
	    catch (InterruptedException ie) {
		return;
	    }
	    catch (InterruptedIOException iioe) {
		return;
	    }
	    catch (IOException ioe) {
		Logger.get().println("reader IOException : "
				   + ioe.toString());
		ie = ioe;
	    }
	}
    }
    
    boolean isNotifier() {
	return notify;
    }
    
    public byte[] read() throws IOException {
	if (ie != null)
	    throw ie;
	return b;
    }
}
class ProveThread extends Thread {
    
    Ab ab;
    String project;
    String name;
    int force;
    RemoteException remoteExc;
    
    ProveThread(Ab ab, String project, String name, int force) {
	this.ab = ab;
	this.name = name;
	this.force = force;
	this.project = project;
	remoteExc = null;
    }
    
    public void run() {
	Logger.err.println(toString() + " is running.");
	try {
	    ab.sendCommand("op " + project + "\n"
			   + "pr " + name + " " + force + "\n");
	}
	catch (RemoteException re) {
	    remoteExc = re;
	}
	Logger.err.println(toString() + " is finished.");
	ab.proofRunning = false;
    }

    RemoteException getRemoteExc() {
	return remoteExc;
    }
}

