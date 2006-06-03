///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: Jab
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jab;

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

public class Jab extends java.rmi.server.UnicastRemoteObject implements eJab {

	/** */
	private static final long serialVersionUID = 1L;
	static String DIR; // = "/export/home/jack/JML2B/";
	static String bbatch; // "/usr/local/atelierb/AB/bbin/sun5.6/bbatch"
	static String AB; //  "/usr/local/atelierb/AB"
	static String ab_def;
	// /usr/local/atelierb/AB/bbin/sun5.6/ab.def.extra_large
	static boolean version3_6;
	static String resourceFile;
	static String exec[];

	static String Printing_Project_list;
	static String InterpretationAborted;

	static void setDir(String dir) {
		DIR = dir;
	}

	static void setBbatch(String bb) {
		bbatch = bb;
	}

	static void setAb(String ab) {
		AB = ab;
	}

	static void setAbdef(String abDef) {
		ab_def = abDef;
	}

	static void setVersion(String v) {
		if (v.equals("3.6"))
			version3_6 = true;
		else if (v.equals("3.5"))
			version3_6 = false;
		else {
			System.err.println(
				"Only 3.5 and 3.6 Atelier B versions are suported.");
			System.exit(1);
		}
	}

	static void setResourceFile(String f) {
		resourceFile = f;
	}

	static void setExec() {
		if (version3_6) {
			exec = new String[2];
			exec[0] = bbatch;
			exec[1] = "-r=" + resourceFile;
			Printing_Project_list = "Printing Project list ...";
			InterpretationAborted = "Interpretation aborted at line ";
		} else {
			exec = new String[3];
			exec[0] = bbatch;
			exec[1] = "-a=" + AB;
			exec[2] = "-d=" + ab_def;
			Printing_Project_list = "Printing Projects list ...";
			InterpretationAborted = "Interpretation aborted in line ";
		}
	}

	static final String LOG = "/0/user/lburdy/Bin/Server/Log/";
	Jip jip;
	boolean debug;

	boolean proofRunning;
	int cptProvedRunning;
	int cptUnprovedRunning;

	public eJab getNewAb() throws java.rmi.RemoteException {
		return new Jab();
	}

	public Jab() throws java.rmi.RemoteException {
		super();
	}

	public boolean checkProject(String project)
		throws java.rmi.RemoteException {
		return (directory = getDirectory(project)) != null;
	}

	private String getDirectory(String project)
		throws java.rmi.RemoteException {
		return DIR + project + "/bdp";
		/*String res = sendCommand("infos_project " + project + "\n");
		int i = res.indexOf("Database path :");
		if (i != -1)
		return res.substring(i+16, res.indexOf('\n', i));
		else
		return null;*/
	}

	public void initialize(boolean debug) throws java.rmi.RemoteException {
		this.debug = debug;
		sendCommand("");
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

			log =
				new FileOutputStream(
					new File(LOG + atelierb.toString() + ".log"));
		} catch (IOException e) {
			throw new RemoteException("Cannot execute Atelier B. ", e);
		}

		int j = 0;

		try {
			j = er.available();
		} catch (IOException e) {
			throw new RemoteException("Cannot read buffer. ", e);
		}

		if (j != 0) {
			b = new byte[j];
			try {
				er.read(b, 0, j);
			} catch (IOException e) {
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
			System.out.println("Command " + command + "\nq\n" + " sent");

			Object sync = new Object();

			Reader inReader = new Reader(this, sync, is);
			Reader errReader = new Reader(this, sync, er);

			pid = null;

			try {

				inReader.start();
				errReader.start();

				lab : do {
					synchronized (sync) {
						sync.notifyAll();
					}
					synchronized (this) {
						while ((!errReader.isNotifier())
							&& (!inReader.isNotifier())) {
							this.wait(5000);
						}
					}
					if (errReader.isNotifier()) {
						byte[] bb = errReader.read();
						log.write(bb);
						throw new RemoteException(new String(bb));
					} else {
						byte[] bb = inReader.read();
						log.write(bb);
						String tmp = new String(bb);
						res += tmp;
						if (proofRunning) {
							for (int k = 0; k < tmp.length(); k++) {
								if (tmp.charAt(k) == '+')
									cptProvedRunning++;
								if (tmp.charAt(k) == '-')
									cptUnprovedRunning++;
							}
							/*krtpid*/
							if (pid == null
								&& res.indexOf('\n', 35) >= 35
								&& res.substring(29, 35).equals("krtpid")) {
								pid = res.substring(35, res.indexOf('\n', 35));
							}
						}

						if (res.length() >= 33
							&& res.substring(
								res.length() - 33,
								res.length() - 2).equals(
								InterpretationAborted)) {
							break lab;
						}
						if (res.length() >= 32
							&& res.substring(
								res.length() - 32,
								res.length() - 11).equals(
								"End of interpretation"))
							break lab;
						inReader.notify = false;
					}
				}
				while (true);
			} finally {
				inReader.interrupt();
				errReader.interrupt();
				log.close();
				atelierb = null;
			}
		} catch (IOException e) {
			throw new RemoteException("Cannot read buffer. ", e);
		} catch (InterruptedException ie) {
			throw new RemoteException("Thread has been interrupted ", ie);
		}
		return res;
	}

	public String[] getProjectList() throws java.rmi.RemoteException {
		Vector projectList = new Vector();
		String res = sendCommand("spl\n");

		res = res.substring(0, res.indexOf("End of Project list"));

		int i =
			res.indexOf(Printing_Project_list)
				+ Printing_Project_list.length()
				+ 1;
		while (i + 7 < res.length()) {
			System.out.println("--> " + res.substring(i + 7, res.length()));
			projectList.add(res.substring(i + 7, i = res.indexOf('\n', i + 7)));
		}
		String[] result = new String[projectList.size()];
		Enumeration e = projectList.elements();
		for (i = 0; i < projectList.size(); i++) {
			result[i] = (String) e.nextElement();
		}
		return result;
	}

	public void newProject(String project) throws java.rmi.RemoteException {
		File f = new File(DIR + project);
		if (!f.exists())
			f.mkdir();
		f = new File(DIR + project + "/bdp");
		if (!f.exists())
			f.mkdir();
		f = new File(DIR + project + "/lang");
		if (!f.exists())
			f.mkdir();
		sendCommand(
			"crp "
				+ project
				+ " "
				+ DIR
				+ project
				+ "/bdp "
				+ DIR
				+ project
				+ "/lang\n");
	}

	public String removeProject(String project)
		throws java.rmi.RemoteException {
		sendCommand("rp " + project + "\n");
		return "";
	}

	String name;
	FileOutputStream fos;
	String directory;

	public boolean addFile(String project, String name)
		throws java.rmi.RemoteException {
		try {
			PrintStream ps =
				new PrintStream(
					new FileOutputStream(
						new File(directory + "/" + name + ".mch")));
			ps.println("MACHINE");
			ps.println("   " + name);
			ps.println("END");
			ps.close();
		} catch (IOException ie) {
			throw new RemoteException(
				"Cannot create " + directory + "/" + name + ".mch");
		}
		this.name = name;
		sendCommand(
			"cd "
				+ directory
				+ "\n"
				+ "op "
				+ project
				+ "\n"
				+ "add_file "
				+ name
				+ ".mch\n"
				+ "t "
				+ name
				+ "\n"
				+ "po "
				+ name
				+ "\n");
		return true;
	}

	public boolean openPo(String project) throws java.rmi.RemoteException {
		try {
			fos =
				new FileOutputStream(new File(directory + "/" + name + ".po"));
		} catch (IOException ioe) {
			throw new RemoteException("Open Po", ioe);
		}
		return true;
	}

	public boolean openPmi(String name, String project)
		throws java.rmi.RemoteException {
		System.out.println("Opening " + directory + "/" + name + ".pmi");
		try {
			fos =
				new FileOutputStream(new File(directory + "/" + name + ".pmi"));
		} catch (IOException ioe) {
			throw new RemoteException("Open Pmi", ioe);
		}
		return true;
	}

	public boolean send(byte[] data) throws java.rmi.RemoteException {
		try {
			fos.write(data);
		} catch (IOException ioe) {
			throw new RemoteException("Send", ioe);
		}
		return true;
	}

	public boolean closePo() throws java.rmi.RemoteException {
		try {
			fos.close();
		} catch (IOException ioe) {
			throw new RemoteException("close Po", ioe);
		}
		return true;
	}

	public boolean closePmi() throws java.rmi.RemoteException {
		try {
			fos.close();
		} catch (IOException ioe) {
			throw new RemoteException("close Pmi", ioe);
		}
		return true;
	}

	FileInputStream fis;
	int available;

	public boolean beginReadPmi(String project, String name)
		throws java.rmi.RemoteException {
		try {
			fis =
				new FileInputStream(
					new File(getDirectory(project) + "/" + name + ".pmi"));
		} catch (IOException ioe) {
			throw new RemoteException("beginning read Pmi", ioe);
		}
		return true;
	}

	public boolean isPmiAvailable() throws java.rmi.RemoteException {
		try {
			return (available = fis.available()) != 0;
		} catch (IOException ioe) {
			throw new RemoteException("Check if Pmi is available", ioe);
		}
	}

	public byte[] read() throws java.rmi.RemoteException {
		try {
			byte[] tmp = new byte[available];
			fis.read(tmp, 0, available);
			return tmp;
		} catch (IOException ioe) {
			throw new RemoteException("Read", ioe);
		}
	}

	public boolean endReadPmi() throws java.rmi.RemoteException {
		try {
			fis.close();
		} catch (IOException ioe) {
			throw new RemoteException("End reading Pmi", ioe);
		}
		return true;
	}

	Process atelierb;
	ProveThread proveThread;
	String pid;

	public void killProofProcess() throws java.rmi.RemoteException {
		if (pid != null) {
			String exec[] = { "/bin/kill", "-13", pid };
			try {
				Runtime.getRuntime().exec(exec);
			} catch (IOException ioe) {
				throw new RemoteException("kill -9 " + pid, ioe);
			}
		}
		if (atelierb != null) {
			System.out.println("Kill proof process. " + atelierb.toString());
			atelierb.destroy();
		}
		if (proveThread != null)
			proveThread.interrupt();
	}

	public void prove(String project, String name, int force)
		throws java.rmi.RemoteException {
		cptProvedRunning = 0;
		cptUnprovedRunning = 0;
		proofRunning = true;
		proveThread = new ProveThread(this, project, name, force);
		proveThread.start();
		RemoteException re = proveThread.getRemoteExc();
		if (re != null)
			throw re;
	}

	public boolean getProofRunning() {
		if (!proofRunning) {
			System.out.println(toString() + " proof no longer running.");
		}
		return proofRunning;
	}

	public int getCptProvedRunning() {
		return cptProvedRunning;
	}

	public int getCptUnprovedRunning() {
		return cptUnprovedRunning;
	}

	public boolean browse(String project, String name)
		throws java.rmi.RemoteException {
		jip = new Jip(project, name, debug);
		return jip.isLaunched;
	}

	public boolean pr(String name, int po, String tactic)
		throws java.rmi.RemoteException {
		return jip.pr(name, po, tactic);
	}

	public boolean fh(String name, int po, String hyp)
		throws java.rmi.RemoteException {
		return jip.fh(name, po, hyp);
	}

	public boolean isProved(String name, int po)
		throws java.rmi.RemoteException {
		return jip.isProved(name, po);
	}

	public boolean[] getStatus(String project, String name, int nbPo)
		throws java.rmi.RemoteException {
		String rep =
			sendCommand(
				"op " + project + "\n" + "b " + name + "\n" + "gs\n" + "qu\n");
		boolean[] res = new boolean[nbPo];
		int current = 0;
		for (int i = 0; i < nbPo; i++) {
			int tmp = rep.indexOf("      PO", current);
			current = rep.indexOf(" ", tmp + 7);
			res[i] = rep.charAt(current + 1) == 'P';
		}
		return res;
	}

	public void quitinteractiveprover() throws java.rmi.RemoteException {
		jip.qu();
	}

	public void q() throws java.rmi.RemoteException {
		sendCommand("q\n");
	}
}

class ProveThread extends Thread {

	Jab ab;
	String project;
	String name;
	int force;
	RemoteException remoteExc;

	ProveThread(Jab ab, String project, String name, int force) {
		this.ab = ab;
		this.name = name;
		this.force = force;
		this.project = project;
		remoteExc = null;
	}

	public void run() {
		System.err.println(toString() + " is running.");
		try {
			ab.sendCommand(
				"op " + project + "\n" + "pr " + name + " " + force + "\n");
		} catch (RemoteException re) {
			remoteExc = re;
		}
		System.err.println(toString() + " is finished.");
		ab.proofRunning = false;
	}

	RemoteException getRemoteExc() {
		return remoteExc;
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
				} else {
					return;
				}
				notify = true;
				synchronized (sync1) {
					sync1.notify();
				}
				synchronized (sync2) {
					while (notify)
						sync2.wait(2000);
				}
			} catch (InterruptedException ie) {
				return;
			} catch (InterruptedIOException iioe) {
				return;
			} catch (IOException ioe) {
				System.out.println("reader IOException : " + ioe.toString());
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
