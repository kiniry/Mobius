///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: eJab
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jab;


public interface eJab extends java.rmi.Remote {

    public eJab getNewAb() throws java.rmi.RemoteException;

    public void initialize(boolean debug) throws java.rmi.RemoteException;

    public boolean checkProject(String project) throws java.rmi.RemoteException;

    public void newProject(String project) throws java.rmi.RemoteException;

    public String removeProject(String project) throws java.rmi.RemoteException;

    public String[] getProjectList() throws java.rmi.RemoteException;

    public boolean addFile(String project, 
			   String name) throws java.rmi.RemoteException;
    
    public boolean openPo(String project) throws java.rmi.RemoteException;
    
    public boolean openPmi(String name, String project) throws java.rmi.RemoteException;
    
    public boolean send(byte[] data) throws java.rmi.RemoteException;
    
    public boolean closePo() throws java.rmi.RemoteException;
    
    public boolean closePmi() throws java.rmi.RemoteException;

    public boolean beginReadPmi(String project, String name)  throws java.rmi.RemoteException;
    
    public boolean isPmiAvailable() throws java.rmi.RemoteException;
    
    public byte[] read() throws java.rmi.RemoteException;

    public boolean endReadPmi() throws java.rmi.RemoteException;
    
    void killProofProcess() throws java.rmi.RemoteException;

    // prove a jmlfile
    public void prove(String project, String name, int force) throws java.rmi.RemoteException;
    
    public boolean getProofRunning() throws java.rmi.RemoteException;

    public int getCptProvedRunning() throws java.rmi.RemoteException;

    public int getCptUnprovedRunning() throws java.rmi.RemoteException;

    // open interactive prover on a jmlfile
    public boolean browse(String project, String name) throws java.rmi.RemoteException;

    public boolean isProved(String name, int po) throws java.rmi.RemoteException;

    public boolean[] getStatus(String project, String name, int nbPo) throws java.rmi.RemoteException;
    
    public boolean pr(String name, int po, String tactic) throws java.rmi.RemoteException;
    
    public boolean fh(String name, int po, String hyp) throws java.rmi.RemoteException;
    
    public void quitinteractiveprover() throws java.rmi.RemoteException;
    
    public void q() throws java.rmi.RemoteException;

}
