//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: eJab.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jab;

/**
 * Remote interface for the Atelier B Server
 **/
public interface eJab extends java.rmi.Remote {

    /**
     * Return a server instance.
     * @return a server instance that will be used in all the other operations.
     * @throws java.rmi.RemoteException
     **/
	eJab getNewAb() throws java.rmi.RemoteException;

	/**
	 * Test if the Atelier B can be run and change the debug mode of the server.
     * @param debug debug mode
     * @throws java.rmi.RemoteException
	 **/
	void initialize(boolean debug) throws java.rmi.RemoteException;

	/**
     * Verify that the parameter is a valid project name.
     * @param project Tested project name
     * @return <code>true</code> if the project exists, <code>false</code> otherwise
     * @throws java.rmi.RemoteException
     **/
    boolean checkProject(String project) throws java.rmi.RemoteException;

    /**
     * Create a new project
     * @param project The project name
     * @throws java.rmi.RemoteException
     **/
	void newProject(String project) throws java.rmi.RemoteException;

    /**
     * Remove a project
     * @param the name of the removed project
     * @throws java.rmi.RemoteException
     **/
	String removeProject(String project) throws java.rmi.RemoteException;

    /**
     * Returns the list of existing project
     * @return the project list
     * @throws java.rmi.RemoteException
     **/
	String[] getProjectList() throws java.rmi.RemoteException;

    /**
     * Add an empty machine to a project.
     * @param project The project name where the machine is added
     * @param name The machine name
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean addFile(String project, String name)
		throws java.rmi.RemoteException;

    /**
     * Open in write mode the .po file of the current machine of the current project.
     * @param project Useless parameter
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean openPo(String project) throws java.rmi.RemoteException;

    /**
     * Open in write mode the .pmi file of a given machine of the current project.
     * @param name The machine name
     * @param project Useless parameter
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean openPmi(String name, String project)
		throws java.rmi.RemoteException;

    /**
     * Store data in the currently open file (.po or .pmi)
     * @param data Data to store
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean send(byte[] data) throws java.rmi.RemoteException;

    /**
     * Close the currently open .po file
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean closePo() throws java.rmi.RemoteException;

    /**
     * Close the currently open .pmi file
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean closePmi() throws java.rmi.RemoteException;

    /**
     * Open in read mode the .pmi file of a given machine of the given project.
     * @param name The machine name
     * @param project The project name
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean beginReadPmi(String project, String name)
		throws java.rmi.RemoteException;

    /**
     * Returns whether there are some data to read in the currently open .pmi
     * @return <code>true</code> if some data can be read, <code>false</code> 
     * otherwise
     * @throws java.rmi.RemoteException
     **/
	boolean isPmiAvailable() throws java.rmi.RemoteException;

    /**
     * Reads data in the currently open .pmi
     * @return the read data
     * @throws java.rmi.RemoteException
     **/
	byte[] read() throws java.rmi.RemoteException;

    /**
     * Closes the currently open .pmi
     * @return <code>true</code>
     * @throws java.rmi.RemoteException
     **/
	boolean endReadPmi() throws java.rmi.RemoteException;

	/**
     * Start a proof process of a given machine of a given project.
     * @param project The project name
     * @param name The machine name
     * @param force The prove force
     * @throws java.rmi.RemoteException
     **/ 
	void prove(String project, String name, int force)
		throws java.rmi.RemoteException;

    /**
     * Tests whereas the proof process is still running.
     * @return <code>true</code> if the proof process is still running, 
     * <code>false</code> otherwise
     * @throws java.rmi.RemoteException
     **/
	boolean getProofRunning() throws java.rmi.RemoteException;

    /**
     * Returns the number of lemma proved by the current proof process
     * @return the number of currently <code>+</code> displayed
     * @throws java.rmi.RemoteException
     **/
	int getCptProvedRunning() throws java.rmi.RemoteException;

    /**
     * Returns the number of lemma not proved by the current proof process
     * @return the number of currently <code>-</code> displayed
     * @throws java.rmi.RemoteException
     **/
	int getCptUnprovedRunning() throws java.rmi.RemoteException;

    /**
     * Kills the current proof process.
     * @throws java.rmi.RemoteException
     **/
	void killProofProcess() throws java.rmi.RemoteException;

	/**
     * Opens the interactive prover on a given machine of a given project
     * @param project The project name
     * @param name The machine name
     * @return <code>true</code> if the interactive prover has been openened, 
     * <code>false</code> otherwise
     * @throws java.rmi.RemoteException
     **/
	boolean browse(String project, String name)
		throws java.rmi.RemoteException;

    /*
     * Returns whether a lemma is proved or not.
     * @param name The operation name
     * @param po The lemma number
     * @return <code>true</code> if the PO is proved, <code>false</code> otherwise
     * @throws java.rmi.RemoteException
     */
	boolean isProved(String name, int po) throws java.rmi.RemoteException;

	boolean[] getStatus(String project, String name, int nbPo)
		throws java.rmi.RemoteException;

    /**
     * Tries to prove a lemma.
     * @param name The operation name
     * @param po The lemma number
     * @param tactic The tactic used to prove the lemma
     * @return <code>true</code> if the PO is proved, <code>false</code> otherwise
     * @throws java.rmi.RemoteException
     **/
	boolean pr(String name, int po, String tactic) throws java.rmi.RemoteException;

    /**
     * Tries to prove a lemma by contradiction.
     * @param name The operation name
     * @param po The lemma number
     * @param hyp The contradictory hypothesis
     * @return <code>true</code> if the PO is proved, <code>false</code> otherwise
     * @throws java.rmi.RemoteException
     **/
	boolean fh(String name, int po, String hyp)
		throws java.rmi.RemoteException;

    /**
     * Close the interactive prover session.
     * @throws java.rmi.RemoteException
     **/
	void quitinteractiveprover() throws java.rmi.RemoteException;

	void q() throws java.rmi.RemoteException;

}
