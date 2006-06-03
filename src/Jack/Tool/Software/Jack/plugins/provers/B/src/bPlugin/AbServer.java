//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: AbServer.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package bPlugin;

import jab.eJab;
import jack.util.Logger;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;

import jpov.JpoFile;
import jpov.JpovError;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.widgets.Shell;

/**
 * This class interfaces the Atelier B.
 * @author L. Burdy
 **/
public class AbServer {

	/**
	 * Displays an error dialog displaying an error coming from the remote 
	 * service
	 * @param shell The current shell
	 * @param title The title of the error dialog
	 * @param error The error to displayed
	 * @param e The remote exception 
	 **/
	public static void remoteExceptionDialog(
		Shell shell,
		String title,
		String error,
		Exception e) {
		JpovError.errorDialogWithDetails(
			shell,
			title,
			error,
			AbServer.getErrorReason(e),
			AbServer.getErrorDetails(e));
	}

	public static AbServer connect(IFile jpo_file, JpoFile jf)
		throws
			RemoteException,
			MalformedURLException,
			NoProjectException,
			NotBoundException {
		return new AbServer(jpo_file, jf);
	}

	/**
	 * Returns the error details from a remote exception.
	 * @param remoteExc The remote exception
	 * @return the message associated with the exception
	 **/
	public static String getErrorDetails(Exception remoteExc) {
		if (remoteExc != null)
			return remoteExc.getMessage();
		else
			return "Remote Exception is null";
	}

	/**
	 * Returns the error reason from a remote exception
	 * @param remoteExc The remote exception
	 * @return an understandable reason extracted from the exception message. 
	 * The reason can be:
	 * <UL>
	 * <li> <i>Server is unreachable</i>
	 * <li> <i>Unknown licence file path</i>
	 * <li> <i>Server is not alive</i>
	 * <li> <i>No licence available</i>
	 * </UL>
	 **/
	public static String getErrorReason(Exception remoteExc) {
		if (remoteExc == null)
			return "Server is unreachable";
		else if (
			remoteExc.getMessage().indexOf("Unknown licence file path") != -1)
			return "Unknown licence file path";
		else if (remoteExc.getMessage().indexOf("Connection refused") != -1)
			return "Server is not alive";
		else if (remoteExc.getMessage().indexOf("No licence available") != -1)
			return "No licence available";
		else
			return "Unknown (see Details)";
	}

	/**
	 * Sets the context class loader and looks up for the requested service.
	 * @param c The class fomr which the class loader is taken
	 * @param config The current configuration.
	 * @return the instance of the found service or <code>null</code> if the 
	 * service is not found.
	 **/
	public static eJab abconnect(java.lang.Class c)
		throws RemoteException, MalformedURLException, NotBoundException {
		if (BPlugin.useRemoteAB()) {
			Thread.currentThread().setContextClassLoader(c.getClassLoader());
			return (eJab) Naming.lookup(BPlugin.getJabRmiUrl());}
		else {
			switch (BPlugin.getABVersion()) {
			case BPreferencePage.VersionB4free :
				return new AbB4Free2_0(BPlugin.getB4freeBbatch(), BPlugin.getB4freeRessource(), BPlugin.getBdp());
			case BPreferencePage.Version36 :
				return new Ab3_6(BPlugin.getB4freeBbatch(), BPlugin.getB4freeRessource(), BPlugin.getBdp());
			default :	
				return new Ab3_5(BPlugin.getB4freeBbatch(), BPlugin.getB4freeRessource(), BPlugin.getAbDef(), BPlugin.getBdp());
			}
		}
	}

	/**
	 * Instance of a remote Atelier B server.
	 **/
	private eJab ab;

	/**
	 * Boolean indicating whether the server is connected.
	 **/
	private boolean connected;

	/**
	 * The name of the Atelier B project
	 **/
	private String project;

	/**
	 * Connects to the Atelier B server.
	 * @param config The current configuration
	 * @param jpoFile The currently displayed jpo file
	 * @throws IOException
	 * @throws NoProjectException
	 **/
	private AbServer(IFile f, JpoFile jpoFile)
		throws
			RemoteException,
			MalformedURLException,
			NoProjectException,
			NotBoundException {

		project = BPlugin.getAbProject(f);
		connect(BPlugin.getJabRmiUrl());
		initialize(true);

		if (project == null || !checkProject()) {
			project = null;
			connected = false;
			ab = null;
			throw new NoProjectException(
				"No valid Atelier B project defined " + "for this project.");
		} else {
			addFile(jpoFile);
		}
	}

	/**
	 * Test if the Atelier B can be run and change the debug mode of the server.
	 * @param debug debug mode
	 * @return <code>true</code> if the Atelier B server is running and if the
	 * Atelier B is runnable, <code>false</code> otherwise
	 * @throws java.rmi.RemoteException
	 **/
	public boolean isConnected() throws RemoteException {
		initialize(true);
		return (ab != null && connected);
	}

	/**
	 * Connects to the Atelier B server.
	 * @param jabServiceAddress adresse of the Atelier B Server rmi service
	 * @throws java.rmi.RemoteException
	 **/
	private void connect(String jabServiceAddress)
		throws RemoteException, MalformedURLException, NotBoundException {
		if (BPlugin.useRemoteAB()) {
			Thread.currentThread().setContextClassLoader(
			getClass().getClassLoader());
		eJab abServer = (eJab) Naming.lookup(jabServiceAddress);
		ab = abServer.getNewAb();
		}
		else {
			switch (BPlugin.getABVersion()) {
			case BPreferencePage.VersionB4free :
				ab =  new AbB4Free2_0(BPlugin.getB4freeBbatch(), BPlugin.getB4freeRessource(), BPlugin.getBdp());
				break;
			case BPreferencePage.Version36 :
				ab =  new Ab3_6(BPlugin.getB4freeBbatch(), BPlugin.getB4freeRessource(), BPlugin.getBdp());
				break;
			default :	
				ab = new Ab3_5(BPlugin.getB4freeBbatch(), BPlugin.getB4freeRessource(), BPlugin.getAbDef(), BPlugin.getBdp());
			break;
			}
			
		}
		connected = true;
	}

	/**
	 * Test if the Atelier B can be run and change the debug mode of the server.
	 * @param debug debug mode
	 * @throws java.rmi.RemoteException
	 **/
	private void initialize(boolean debug) throws RemoteException {
		if (ab != null) {
			try {
				ab.initialize(debug);
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
	}

	/**
	 * Verify that the parameter is a valid project name.
	 * @param project Tested project name
	 * @return <code>true</code> if the server is running and if the project exists,
	 *  <code>false</code> otherwise
	 * @throws java.rmi.RemoteException
	 **/
	private boolean checkProject() throws RemoteException {
		if (ab != null) {
			try {
				return ab.checkProject(project);
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}
		}
		return false;
	}

	/**
	 * Add an empty machine to a project and transfer its .po file to the server.
	 * @param project The project name where the machine is added
	 * @param name The machine name
	 * @param directory The directory where is located the .po file
	 * @throws java.rmi.RemoteException
	 **/
	private void addFile(JpoFile jpof) throws RemoteException {
		FileInputStream fis;
		byte[] tmp;
		int i;

		if (ab != null) {
			try {
				if (ab.addFile(project, jpof.getName())) {
					if (ab.openPo(project)) {
						fis =
							new FileInputStream(
								new File(
									jpof.getDirectory(),
									jpof.getName() + ".po"));
						while ((i = fis.available()) != 0) {
							tmp = new byte[i];
							fis.read(tmp, 0, i);
							ab.send(tmp);
						}
						ab.closePo();
					}
				}
			} catch (RemoteException re) {
				connected = false;
				throw re;
			} catch (IOException ie) {
			}
		}
	}

	/**
	 * Transfers a .pmi file from the server to a locale file.
	 * @param project The project name
	 * @param name The machine name
	 * @param directory The directory where the .pmi file is saved
	 * @throws java.rmi.RemoteException
	 **/
	void readPmi(String name, File directory) throws RemoteException {
		byte[] tmp;
		if (ab != null) {
			try {
				ab.beginReadPmi(project, name);
				FileOutputStream fis =
					new FileOutputStream(new File(directory, name + ".pmi"));
				while (ab.isPmiAvailable()) {
					tmp = ab.read();
					fis.write(tmp);
				}
				ab.endReadPmi();
				fis.close();
			} catch (java.rmi.RemoteException re) {
				connected = false;
				throw re;
			} catch (IOException re) {
				Logger.get().println(re.toString());
			}
		}
	}

	/**
	 * Transfers a pmi file to the server and launch a proof on a machine.
	 * @param name The machine name
	 * @param directory The directory where the .pmi file is located
	 * @param force The prover force
	 * @return <code>true</code> if the server is alive, <code>false</code> 
	 * otherwise
	 * @throws java.rmi.RemoteException
	 **/
	public boolean prove(String name, File directory, int force)
		throws RemoteException {

		if (ab != null) {
			try {
				loadPmi(name, directory);
				ab.prove(project, name, force);
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}
		}
		return true;
	}

	/**
	 * Tests whereas the proof process is still running.
	 * @return <code>true</code> if the proof process is still running, 
	 * <code>false</code> otherwise
	 * @throws java.rmi.RemoteException
	 **/
	public boolean getProofRunning() throws RemoteException {
		if (ab != null) {
			try {
				return ab.getProofRunning();
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}
		}
		return false;
	}

	/**
	 * Returns the number of lemma proved by the current proof process
	 * @return the number of currently <code>+</code> displayed
	 * @throws java.rmi.RemoteException
	 **/
	public int getCptProvedRunning() throws RemoteException {
		if (ab != null) {
			try {
				return ab.getCptProvedRunning();
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
		return 0;
	}

	/**
	 * Returns the number of lemma not proved by the current proof process
	 * @return the number of currently <code>-</code> displayed
	 * @throws java.rmi.RemoteException
	 **/
	public int getCptUnprovedRunning() throws RemoteException {
		if (ab != null) {
			try {
				return ab.getCptUnprovedRunning();
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
		return 0;
	}

	/**
	 * Transfers a pmi file to the server.
	 * @param project The project name
	 * @param name The machine name
	 * @param directory The directory where the .pmi file is located
	 * @throws java.rmi.RemoteException
	 **/
	private void loadPmi(String name, File directory) throws RemoteException {
		FileInputStream fis;
		byte[] tmp;
		int i;
		try {
			if (ab.openPmi(name, project)) {
				fis = new FileInputStream(new File(directory, name + ".pmi"));
				while ((i = fis.available()) != 0) {
					tmp = new byte[i];
					fis.read(tmp, 0, i);
					ab.send(tmp);
				}
				ab.closePmi();
			}
		} catch (RemoteException re) {
			connected = false;
			throw re;
		} catch (IOException ioe) {
			throw new RemoteException("IOException ", ioe);
		}
	}

	/**
	 * Transfers a pmi file to the server and opens the interactive prover on a 
	 * given machine of a given project
	 * @param project The project name
	 * @param name The machine name
	 * @param directory The directory where the .pmi file is located
	 * @return <code>true</code> if the server is running and the interactive 
	 * prover has been openened, <code>false</code> otherwise
	 * @throws java.rmi.RemoteException
	 **/
	public boolean browse(String name, File directory) throws RemoteException {

		if (ab != null) {
			loadPmi(name, directory);
			try {
				return ab.browse(project, name);
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}
		}
		return false;
	}

	/**
	 * Tries to prove a lemma.
	 * @param name The operation name
	 * @param po The lemma number
	 * @param tactic The tactic used to prove the lemma
	 * @return <code>true</code> if the server is running and the PO is proved, 
	 * <code>false</code> otherwise
	 * @throws java.rmi.RemoteException
	 **/
	public boolean pr(String name, int po, String tactic)
		throws RemoteException {
		if (ab != null) {
			try {
				return ab.pr(name, po, tactic);
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
		return false;
	}

	/**
	 * Tries to prove a lemma by contradiction.
	 * @param name The operation name
	 * @param po The lemma number
	 * @param hyp The contradictory hypothesis
	 * @return <code>true</code> if the server is running and the PO is proved, 
	 * <code>false</code> otherwise
	 * @throws java.rmi.RemoteException
	 **/
	boolean fh(String name, int po, String hyp) throws RemoteException {
		if (ab != null) {
			try {
				return ab.fh(name, po, hyp);
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
		return false;
	}

	/**
	 * Close the interactive prover session.
	 * @throws java.rmi.RemoteException
	 **/
	public void quitinteractiveprover() throws RemoteException {
		if (ab != null) {
			try {
				ab.quitinteractiveprover();
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
	}

	/**
	 * Kills the current proof process.
	 * @throws java.rmi.RemoteException
	 **/
	public void abortProof() throws RemoteException {
		if (ab != null) {
			try {
				ab.killProofProcess();
			} catch (RemoteException re) {
				connected = false;
				throw re;
			}

		}
	}

	/**
	 * Returns the project.
	 * @return String
	 */
	public String getProject() {
		return project;
	}

}
